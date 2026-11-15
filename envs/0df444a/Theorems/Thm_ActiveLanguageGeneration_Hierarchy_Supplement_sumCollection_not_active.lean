-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_sumCollection_not_active
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.sumCollection_not_active
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:30:40.251062+00:00
-- url     : https://prove2.me/theorems/dc5dcafb-96cc-4dee-a808-4db1258dded9
-- title:
--   Lemma B.6 — C_k is not actively (k−1)-generatable
-- statement:
--   For every integer $k\ge2$, the sum-configuration collection $C_k$ over the positive integers is not actively $(k-1)$-generatable (with repetition): no generator whatsoever is correct at every time $t\ge k-1$ on some full repetition-free enumeration of every $L\in C_k$.
--
--   $$
--   \forall k\ge2:\quad C_k\notin\mathrm{Act}^{k-1}_{\mathrm R}.
--   $$
--
--   This is the lower bound in the separation of Theorem B.3.
--
--   **Formalization Note** The statement covers every generator; the reduction to generators that never output one of their inputs is part of the paper's proof, not an assumption.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} → ℕ+; reason: the paper's positive integers exactly
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Lemma B.6, printed p.28 (PDF p.29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_SumCollection

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Lemma B.6, printed p.28 (PDF p.29): no generator whatsoever actively `(k-1)`-generates `C_k`. -/
theorem sumCollection_not_active (k : ℕ) (hk : 2 ≤ k) :
    ¬ ActiveKGeneratable .R (sumCollection k) (k - 1) := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
