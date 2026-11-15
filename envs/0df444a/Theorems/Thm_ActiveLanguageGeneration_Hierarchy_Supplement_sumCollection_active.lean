-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_sumCollection_active
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.sumCollection_active
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:30:10.913502+00:00
-- url     : https://prove2.me/theorems/813ccad3-37b1-498f-8ab8-011c35c52030
-- title:
--   Lemma B.5 — C_k is actively k-generatable
-- statement:
--   For every integer $k\ge2$, the sum-configuration collection $C_k$ over the positive integers (infinite $L\subseteq\mathbb N$ containing distinct $y_1,\ldots,y_{k+1}$ with $y_1+\cdots+y_k=y_{k+1}$) is actively $k$-generatable (with repetition).
--
--   $$
--   \forall k\ge2:\quad C_k\in\mathrm{Act}^{k}_{\mathrm R}.
--   $$
--
--   This is the upper bound in the separation of Theorem B.3.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} → ℕ+; reason: the paper's positive integers exactly
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Lemma B.5, printed p.28 (PDF p.29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_SumCollection

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Lemma B.5, printed p.28 (PDF p.29). -/
theorem sumCollection_active (k : ℕ) (hk : 2 ≤ k) :
    ActiveKGeneratable .R (sumCollection k) k := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
