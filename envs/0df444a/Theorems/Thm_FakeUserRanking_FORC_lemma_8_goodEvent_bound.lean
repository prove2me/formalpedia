-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_8_goodEvent_bound
-- name    : FakeUserRanking.FORC.lemma_8_goodEvent_bound
-- status  : Disproved
-- author  : @kmehltretter82
-- created : 2026-10-27T06:25:12.280339+00:00
-- url     : https://prove2.me/theorems/eaa7b53b-20aa-49b4-b7f7-5281d55ce19e
-- title:
--   Lemma 8: Good-Event Feedback Regret Bound for FORC
-- statement:
--   Under the good event $G = G_1 \cap G_2$, the expected cumulative gap-weighted feedback count $\sum_{j < i} \Delta_{j,i} \sum_{t=1}^T \mathbf{1}\{\mathcal{E}_{t,j,i}\}$, combined with the direct fake-user term $F$ and the failure-event term $1/n^2$, is bounded above by $300 (n^2 F + \log T) \sum_{j < i} \frac{\log(nT)}{\Delta_{j,i}}$.
-- source:
--   Fake Users in Online Ranking and Recommendation (FORC), Lemma 8 and Proof of Theorem 3, pp. 26–31

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

open Classical in
theorem lemma_8_goodEvent_bound (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)) :
    (F : ℝ) + 1 / (n : ℝ) ^ 2 +
      expect inst P (forc n T tb fb) T
        (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
          ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
            ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
      300 * (((n : ℝ) ^ 2 * F + Real.log T) *
        ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by sorry

end FakeUserRanking.FORC
