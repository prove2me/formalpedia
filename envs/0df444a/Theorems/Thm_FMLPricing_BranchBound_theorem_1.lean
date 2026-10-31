-- Prove2me | Theorems.Thm_FMLPricing_BranchBound_theorem_1
-- name    : FMLPricing.BranchBound.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:42.076563+00:00
-- url     : https://prove2.me/theorems/3fb4053c-722e-44c4-9359-3283a1c4773c
-- title:
--   Theorem 1, p. 19 — BNB(ε) terminates and returns a price vector with revenue at least (1 − ε) times the maximum, for any valid locally Lipschitz bounding rule
-- statement:
--   Fix an FML instance satisfying the standing assumptions and let $\varepsilon > 0$. Run Algorithm 1, $\mathrm{BNB}(\varepsilon)$, with:
--
--   1. a bounding rule $U(x, r)$ in place of $\pi^u$ (line 13–14) that, for some constant $K_0$ and all $x \in X$, $r > 0$, satisfies
--   $$
--   \text{(U1)}\ \ \pi(\tilde x) \le U(x, r) \ \text{ for all } \tilde x \in R(x, r) \cap X, \qquad \text{(U2)}\ \ U(x, r) \le \pi(x) + r K_0;
--   $$
--   2. any choice of solution of $\mathrm{LP}(x, r)$ on line 9, whenever $x$ has positive entries, $r > 0$ and the LP is feasible;
--   3. any order of visiting the centers of $\mathcal X_1$ on line 8.
--
--   Then the while loop of line 5 exits after finitely many passes. At the first exit the incumbent $x^\star$ lies in $X$, and $\texttt{cnstr-rev}(x^\star)$ has a maximizer. $\Pi$ has a global maximizer, and for every maximizer $z'$ of $\texttt{cnstr-rev}(x^\star)$ the price vector $p' = (-\log z'_1 / b_1, \dots, -\log z'_n / b_n)$ satisfies
--   $$
--   \Pi(p') \ge (1 - \varepsilon) \max_{p \in \mathbb R^n} \Pi(p). \tag{20}
--   $$
--
--   This is the paper's approximation guarantee: branch and bound over no-purchase probabilities yields $(1 - \varepsilon)$-optimal prices for the non-concave FML revenue.
--
--   **Formalization Note** The paper's own rule $\pi^u$ (12) is the minimum of three bounds (Propositions 4, 5 and 6). Its Proposition 4 is false as printed: for $m = n = 2$, $a = ((0.07, -2.6), (-0.32, -0.3))$, $b = (1.6, 1.57)$, $w = (0.17, 0.83)$ $r = 0.001$ and $x = q_0(p)$ with $p_j = \underline p_j + (0.4, 0.7)_j (\bar p_j - \underline p_j)$, the point $x + r(1,1) \in R(x, r) \cap X$ has larger $\pi$ than $\pi(x) + r L(x, r)$. So $\pi^u$ is not posed. The proof of Theorem 1 uses only (U1) (line 13 never discards a box holding a maximizer, and the final chain (c)–(d)) and (U2) (step (a) of (44)–(45)), so the theorem is stated for every rule with these two properties. (U1) and (U2) hold together exactly when $\pi$ is $K_0$-Lipschitz on $X$ in the sup norm, e.g. with $U(x, r) = \pi(x) + r K_0$. Such a $K_0$ exists because the polyhedral feasible sets of $\texttt{cnstr-rev}$ move Lipschitz-continuously with $\mu(x)$, and Proposition 5 claims an explicit one. Other conventions are as in the definitions file: the line-8 loop is a left fold over an enumeration of the finite set $\mathcal X_1$, and $\bar\pi$ lives in $[-\infty, \infty]$. For $\varepsilon \ge 1$ the loop exits at once, and $p' = \underline p$ satisfies (20) because $\Pi(\underline p) > 0$. Further departures: $x^\star$ starts at $q_0(\underline p)$, and $\mathrm{LP}(x, r)$ uses the two-sided form of (15)–(16) (see Proposition 7). With the printed form, line 9 has no solution at the first pass on some instances, e.g. $m = 2$, $n = 1$, $a = (-3, 3)$, $b = 1$. The maximum in (20) is read at every global maximizer $p^\star$, whose existence is part of the conclusion.
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), p. 19, Theorem 1 and Algorithm 1 p. 18 (proof pp. 45–46)

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

namespace FMLPricing.BranchBound

/-- Theorem 1, p. 19, for Algorithm 1 `BNB(ε)` (p. 18) run with any bounding rule `U` that
is valid on `R(x, r) ∩ X` (U1) and exceeds `π(x)` by at most `r K₀` (U2), any choice of LP
solution on line 9, and any visiting order on line 8: the `while` loop exits after finitely
many passes, and every maximizer `z'` of `cnstr-rev(x⋆)` gives a price vector
`p' = (−b_j⁻¹ log z'_j)_j` with `Π(p') ≥ (1 − ε) max_{p ∈ ℝⁿ} Π(p)`. -/
theorem theorem_1 {m n : ℕ} (I : FML m n) (hI : Standing I) (ε : ℝ) (hε : 0 < ε)
    (U : (Fin m → ℝ) → ℝ → ℝ) (K₀ : ℝ)
    (hU1 : ∀ x ∈ Xset I, ∀ r > 0, ∀ x' ∈ Rbox I x r ∩ Xset I, piX I x' ≤ U x r)
    (hU2 : ∀ x ∈ Xset I, ∀ r > 0, U x r ≤ piX I x + r * K₀)
    (sol : (Fin m → ℝ) → ℝ → LPVars m n)
    (hsol : ∀ x r, (∀ c, 0 < x c) → 0 < r → LPFeasible I x r → IsLPSolution I x r (sol x r))
    (enum : Finset (Fin m → ℝ) → List (Fin m → ℝ))
    (henum : ∀ S, (enum S).Nodup ∧ (enum S).toFinset = S) :
    ∃ k : ℕ, ¬ bnbCond ε (bnbRun I U sol enum k) ∧
      (∀ j < k, bnbCond ε (bnbRun I U sol enum j)) ∧
      (bnbRun I U sol enum k).xs ∈ Xset I ∧
      (∃ z', IsCnstrMax I (bnbRun I U sol enum k).xs z') ∧
      (∃ pstar : Fin n → ℝ, ∀ p, Pi I p ≤ Pi I pstar) ∧
      ∀ z', IsCnstrMax I (bnbRun I U sol enum k).xs z' →
        ∀ pstar : Fin n → ℝ, (∀ p, Pi I p ≤ Pi I pstar) →
          (1 - ε) * Pi I pstar ≤ Pi I (priceOf I z') := by sorry

end FMLPricing.BranchBound
