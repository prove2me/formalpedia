-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_Supplement_section_B_1
-- name    : BayesGroupHard.VertexCover.Supplement.section_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:46:43.56517+00:00
-- url     : https://prove2.me/theorems/a799ae81-8bba-4ab9-9898-6dac25ecff25
-- title:
--   §B.1, p. 33 — NO case: Σ = {(0,1,…,1)}, φ_i,2 = 2ℓ_0 + n log(3/2), so µ_i,2(0) < exp(−Ω(n))
-- statement:
--   Consider the EXACT-COVER reduction network of Appendix B with $\ell_0=\log\tfrac34$.
--
--   1. If the RXC3 instance $\hat{\mathcal G}_n$ has no exact cover, then $\Sigma=\{(0,1,\dots,1)\}$, and on every signal profile realising the history (19)
--   $$\phi_{i,2}=\log\frac{(1-\bar p^\star)\bar p^{\,n}}{(1-\underline p^\star)\underline p^{\,n}}=2\ell_0+n\log\tfrac32,\qquad \mu_{i,2}(0)=\frac1{1+e^{\phi_{i,2}}}.$$
--   2. There are constants $c>0$ and $N$, independent of the instance, such that for every NO instance with $n\ge N$ and every profile realising (19),
--   $$\mu_{i,2}(0)<e^{-cn}.$$
--
--   This is the NO half of the belief gap behind Theorem 2: without an exact cover, agent $i$ is almost certain that $\theta=1$.
--
--   **Formalization Note.** $n$ is the number of elements (equal to the number of subsets); the network has $2n+2$ agents.
--
--   Differences from the source:
--   - reading: φ_i,2 > Ω(n) and µ_i,2(0) < exp(−Ω(n)) → the exact value of φ_i,2 and ∃ c > 0, ∃ N, uniform over instances, with µ_i,2(0) < exp(−c n) for n ≥ N; reason: the usual meaning of the asymptotic notation, with the constants chosen before the instance.
--   - encoding: agent i receives no private signal → a fair-coin signal of i; reason: a non-informative signal changes no posterior.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 33, §B.1

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network

namespace BayesGroupHard.VertexCover.Supplement

open Finset

/-- §B.1, p. 33 (NO case): without an exact cover, `Σ = {(0,1,…,1)}`, agent `i`'s time-two
log-belief ratio is exactly `2ℓ_0 + n log(3/2)` and `µ_i,2(0) = 1/(1 + e^{φ_i,2})`; and there are
`c > 0` and `N`, independent of the instance, with `µ_i,2(0) < exp(-c n)` for every NO instance
with `n ≥ N`. -/
theorem section_B_1 :
    (∀ {n : ℕ} (X : RXC3 n), ¬ HasCover X →
      sigma X = {baseProfile n} ∧
      ∀ s : XAgent n → Bool, Observed X s →
        rLog (xcNet X) 2 observer s = 2 * ellZero + (n : ℝ) * Real.log (3 / 2) ∧
        belief (xcNet X) 2 observer s false =
          1 / (1 + Real.exp (rLog (xcNet X) 2 observer s))) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ X : RXC3 n, ¬ HasCover X →
      ∀ s : XAgent n → Bool, Observed X s →
        belief (xcNet X) 2 observer s false < Real.exp (-c * n) := by sorry

end BayesGroupHard.VertexCover.Supplement
