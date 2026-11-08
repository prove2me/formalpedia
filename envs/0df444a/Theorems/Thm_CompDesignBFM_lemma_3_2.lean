-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_3_2
-- name    : CompDesignBFM.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:04.368783+00:00
-- url     : https://prove2.me/theorems/303d2d1d-7ed4-4c65-8f04-54dfbbc4bfc4
-- title:
--   Lemma 3.2 — the marginal-contribution rule is nonnegative and budget feasible
-- statement:
--   Let $F$ be normalized and self-bounding, and let $B>0$. For every participating set $S$, the marginal-contribution payments (7) satisfy
--
--   $$p^F_i(S)\ge0\ \text{ for all } i,\qquad \sum_{i\in S}p^F_i(S)\le B.$$
--
--   Differences from the source: none.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 3.2, p.14 (PDF 16)

import Mathlib
import Definitions.Def_CompDesignBFM_IsSelfBounding
import Definitions.Def_CompDesignBFM_mcPay

namespace CompDesignBFM

/-- Lemma 3.2, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.14, PDF 16. If `F` is normalized and self-bounding, then the marginal-contribution
payment rule (7) is nonnegative and budget feasible, at every participating set `S`. -/
theorem lemma_3_2 {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (hB : 0 < B) (hF0 : F ∅ = 0)
    (hF : IsSelfBounding F) (S : Finset (Fin n)) :
    (∀ i, 0 ≤ mcPay F B S i) ∧ ∑ i ∈ S, mcPay F B S i ≤ B := by sorry

end CompDesignBFM
