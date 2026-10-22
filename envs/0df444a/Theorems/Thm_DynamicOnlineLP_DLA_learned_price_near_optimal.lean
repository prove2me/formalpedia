-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_learned_price_near_optimal
-- name    : DynamicOnlineLP.DLA.learned_price_near_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:42:39.492657+00:00
-- url     : https://prove2.me/theorems/db9873f4-da85-4898-8519-cffb1a226c4d
-- title:
--   Lemma 6 — with probability 1 − ε, Σ_{t≤2ℓ} π_t x_t(p̂^ℓ) ≥ (1 − 2h_ℓ − ε) OPT_{2ℓ}((2ℓ/n) b) for all ℓ ∈ L
-- statement:
--   Under the setting of Lemma 5 (an online LP instance with $m\ge1$ constraints, $\pi_t\ge0$, $a_t\in[0,1]^m$, in general position and in uniformly random order; $\varepsilon=2^{-E}$, $E\ge1$, $\varepsilon n$ a positive integer; $L$, $h_\ell$ and the learned dual prices $\hat p^\ell$ of (13) as there), let $\mathrm{OPT}_s(d)$ denote the optimal value of the partial program $\mathrm{LP}_s(d)$ on the first $s$ arrivals with right-hand side $d$. There is an absolute constant $C>0$ such that, if $B=\min_ib_i\ge C\,m\log(n/\varepsilon)/\varepsilon^2$, then with probability at least $1-\varepsilon$, for all $\ell\in L$,
--
--   $$\sum_{t=1}^{2\ell}\pi_t\,x_t(\hat p^{\ell})\ \ge\ (1-2h_\ell-\varepsilon)\,\mathrm{OPT}_{2\ell}\Big(\frac{2\ell}{n}\,b\Big).$$
--
--   This is the optimality half of the analysis: the price learned from the first $\ell$ arrivals, applied to the first $2\ell$ arrivals, is nearly optimal for the proportionally scaled partial program.
--
--   **Formalization Note** The paper's condition is $B\ge10m\log(n/\varepsilon)/\varepsilon^2$; as for Lemma 5, its proof does not deliver the constant $10$, and an absolute constant $C$ quantified before every instance parameter is used instead. The probability $1-\varepsilon$ and the factor $1-2h_\ell-\varepsilon$ are exact. $\log$ is the natural logarithm; times $1,\dots,2\ell$ are Lean's `firstTimes n (2ℓ)`.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 884, Lemma 6 (proof: p. 884 and p. 888, Appendix B.2)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_DynamicOnlineLP_DLA_Algorithm

namespace DynamicOnlineLP.DLA

/-- Lemma 6 (Agrawal–Wang–Ye 2014, p. 884), with an absolute constant `C` in place of the paper's
`10`: under Assumptions 1–3, `ε = 2^{-E}` and `εn ∈ ℕ`, if `b_i ≥ C m log(n/ε)/ε²` for all `i`,
then with probability at least `1 - ε` over the arrival order, for all `ℓ ∈ L`,
`∑_{t=1}^{2ℓ} π_t x_t(p̂^ℓ) ≥ (1 - 2h_ℓ - ε) OPT_{2ℓ}((2ℓ/n) b)`. -/
theorem learned_price_near_optimal :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n E : ℕ) (I : Instance m n) (rule : DualRule m n),
        1 ≤ m → 1 ≤ E → 0 < n → 2 ^ E ∣ n → I.GeneralPosition → IsValidDualRule rule →
        (∀ i : Fin m, C * (m : ℝ) * Real.log ((n : ℝ) / eps E) / eps E ^ 2 ≤ I.b i) →
        1 - eps E ≤ probPerm (fun σ : Equiv.Perm (Fin n) =>
          ∀ ℓ ∈ phases n E,
            (1 - 2 * slack n E ℓ - eps E) *
                I.partialOPT σ (2 * ℓ) (fun i => (2 * (ℓ : ℝ) / (n : ℝ)) * I.b i) ≤
              ∑ t ∈ firstTimes n (2 * ℓ),
                I.arrPi σ t * threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t) := by sorry

end DynamicOnlineLP.DLA
