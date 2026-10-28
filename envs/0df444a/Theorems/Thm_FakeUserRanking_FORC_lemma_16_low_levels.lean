-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_16_low_levels
-- name    : FakeUserRanking.FORC.lemma_16_low_levels
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T07:36:43.546435+00:00
-- url     : https://prove2.me/theorems/a8303800-c727-497e-841e-047611ae9186
-- title:
--   Lemma 16, p. 58 — Expected Sub-Optimal Feedback Bound on Low Levels (2^l < F)
-- statement:
--   **Low-Level Sub-Optimal Feedback Bound on $\mathcal G$ (Lemma 16, pp. 58–62).** There exists an absolute constant $C > 0$ such that for all $n \ge 1$, $T \ge 2$, $F \ge 0$, every instance with strictly decreasing click probabilities $\mu_1 > \dots > \mu_n$, every adaptive policy $\mathbf P$ within fakeness budget $F$, every resolution of FORC's tie-breaking and fallback rules, and every pair of products $j < i$,
--
--   $$\mathbb E\left[\mathbf 1_{\mathcal G}\sum_{t=1}^T \mathbf 1\big\{2^{\ell_t} < F \,\wedge\, A_{r,t}(\pi_t(j)=i)\big\}\right] \le C\,n^2 F\,\frac{\log(nT)}{\Delta_{j,i}^2}.$$
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, Appendix D, Lemma 16, pp. 58-62

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

open Classical in
/-- Lemma 16 (Low-Level Bound, pp. 58–62): there is an absolute constant `C` such that for every
pair of products `j < i`, the expected number of rounds on event `G` in which a low level
`2^(k+1) < F` is sampled and `feedbackEvent` occurs for `(j, i)` is at most
`C n² F log(nT) / Δ_{j,i}²`. -/
theorem lemma_16_low_levels :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
      ∀ (j i : Fin n), j < i →
        expect inst P (forc n T tb fb) T
          (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
            ∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧
              feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
          C * ((n : ℝ) ^ 2 * F * (Real.log ((n : ℝ) * T) / gap inst j i ^ 2)) := by sorry

end FakeUserRanking.FORC
