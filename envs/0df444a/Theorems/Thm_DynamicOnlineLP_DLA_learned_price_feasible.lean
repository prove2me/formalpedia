-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_learned_price_feasible
-- name    : DynamicOnlineLP.DLA.learned_price_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:39:19.195981+00:00
-- url     : https://prove2.me/theorems/a0f6681b-583d-49bc-9fec-a160c7c5663a
-- title:
--   Lemma 5 — with probability 1 − ε the learned prices never overspend: Σ_{t=ℓ+1}^{2ℓ} a_it x_t(p̂^ℓ) ≤ (ℓ/n) b_i for all i and ℓ ∈ L
-- statement:
--   Consider an instance of the online linear program with $n$ columns ($\pi_t\ge0$, $a_t\in[0,1]^m$, $m\ge1$) in general position, arriving in a uniformly random order. Let $\varepsilon=2^{-E}$ with $E\ge1$, assume $\varepsilon n$ is a positive integer, let $L=\{\varepsilon n,2\varepsilon n,\dots,2^{E-1}\varepsilon n\}$, $h_\ell=\varepsilon\sqrt{n/\ell}$, and let $\hat p^{\ell}$ be an optimal dual price of the partial LP (13) on the first $\ell$ arrivals (chosen by any valid dual-selection rule). There is an absolute constant $C>0$ such that, if
--
--   $$B=\min_i b_i\ge \frac{C\,m\log(n/\varepsilon)}{\varepsilon^2},$$
--
--   then with probability at least $1-\varepsilon$ over the arrival order,
--
--   $$\sum_{t=\ell+1}^{2\ell}a_{it}\,x_t(\hat p^{\ell})\le\frac{\ell}{n}\,b_i\qquad\text{for all } i\in\{1,\dots,m\},\ \ell\in L.$$
--
--   Here $x_t(\hat p^\ell)$ is the threshold decision for the column arriving at time $t$. The lemma says that in each doubling period the decisions induced by the price learned at its start consume at most that period's proportional share of every resource, which is what keeps the dynamic learning algorithm from running out of capacity.
--
--   **Formalization Note** The paper states the condition as $B\ge 10m\log(n/\varepsilon)/\varepsilon^2$. Its proof (Appendix B.1) does not close with the constant $10$ (the union-bound step needs $4mE\varepsilon^{m-1}\le1$, false for $m=1$, and the count of distinct threshold patterns by $n^m$ is too small), so the statement uses an absolute constant $C$, quantified before every instance parameter; everything else is exact, including the probability $1-\varepsilon$. $\log$ is the natural logarithm. Times are 0-based in Lean, so the paper's times $\ell+1,\dots,2\ell$ are Lean times $\ell,\dots,2\ell-1$. General position (Assumption 3), a standing assumption of the paper's analysis, is a hypothesis.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 884, Lemma 5 (proof: p. 888, Appendix B.1)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_DynamicOnlineLP_DLA_Algorithm

namespace DynamicOnlineLP.DLA

/-- Lemma 5 (Agrawal–Wang–Ye 2014, p. 884), with an absolute constant `C` in place of the paper's
`10`: under Assumptions 1–3, `ε = 2^{-E}` and `εn ∈ ℕ`, if `b_i ≥ C m log(n/ε)/ε²` for all `i`,
then with probability at least `1 - ε` over the arrival order,
`∑_{t=ℓ+1}^{2ℓ} a_{it} x_t(p̂^ℓ) ≤ (ℓ/n) b_i` for all `i` and all `ℓ ∈ L`
(paper times `ℓ+1, …, 2ℓ` are the 0-based times `ℓ, …, 2ℓ−1`). -/
theorem learned_price_feasible :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n E : ℕ) (I : Instance m n) (rule : DualRule m n),
        1 ≤ m → 1 ≤ E → 0 < n → 2 ^ E ∣ n → I.GeneralPosition → IsValidDualRule rule →
        (∀ i : Fin m, C * (m : ℝ) * Real.log ((n : ℝ) / eps E) / eps E ^ 2 ≤ I.b i) →
        1 - eps E ≤ probPerm (fun σ : Equiv.Perm (Fin n) =>
          ∀ ℓ ∈ phases n E, ∀ i : Fin m,
            ∑ t ∈ Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ),
                I.arrA σ t i *
                  threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t ≤
              ((ℓ : ℝ) / (n : ℝ)) * I.b i) := by sorry

end DynamicOnlineLP.DLA
