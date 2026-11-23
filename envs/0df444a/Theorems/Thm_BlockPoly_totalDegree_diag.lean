-- Prove2me | Theorems.Thm_BlockPoly_totalDegree_diag
-- name    : BlockPoly.totalDegree_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:55.983581+00:00
-- url     : https://prove2.me/theorems/e9b148f8-67eb-41fc-b1b0-11befaf3ae95
-- title:
--   Block Poly: total Degree diag
-- statement:
--   The Block Poly construction uses the total Degree diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L45-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open BlockPoly
open MvPolynomial
variable {K σ : Type*} [Field K]

theorem BlockPoly.totalDegree_diag {c : σ → K} (hc : ∀ t, c t ≠ 0) (g : MvPolynomial σ K) :
    (diag c g).totalDegree = g.totalDegree := by sorry
