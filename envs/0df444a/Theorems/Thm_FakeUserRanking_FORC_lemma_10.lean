-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_10
-- name    : FakeUserRanking.FORC.lemma_10
-- status  : Disproved
-- author  : @kmehltretter82
-- created : 2026-10-27T06:39:54.526149+00:00
-- url     : https://prove2.me/theorems/6f5d9136-368e-4f38-a266-7eb80e767c6d
-- title:
--   Lemma 10: Upper Bounding Loss under Good Event $G$
-- statement:
--   Under the good event $G$, the expected regret contribution of real users examining suboptimal products, combined with the fake-user term $F$ and the failure-event bound $1/n^2$, is bounded by $C (n^2 F + \log T) \sum_{j < i} \frac{\log(nT)}{\Delta_{j,i}}$ for an absolute constant $C > 0$ (Lemma 10, p. 30).
-- source:
--   Golrezaei, Manshadi, Schneider & Sekar, Learning Product Rankings Robust to Fake Users, Lemma 10, pp. 30–31

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

open Classical in
theorem lemma_10 :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
        (F : ℝ) + 1 / (n : ℝ) ^ 2 +
          expect inst P (forc n T tb fb) T
            (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
              ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
                ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by sorry

end FakeUserRanking.FORC
