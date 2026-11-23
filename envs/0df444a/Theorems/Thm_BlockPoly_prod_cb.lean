-- Prove2me | Theorems.Thm_BlockPoly_prod_cb
-- name    : BlockPoly.prod_cb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:57.818251+00:00
-- url     : https://prove2.me/theorems/bef791c9-8074-4a42-a584-b421d32089af
-- title:
--   Block Poly: prod cb
-- statement:
--   The Block Poly construction uses the prod cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L92-L98

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
variable {K : Type*} [Field K] {D N : ℕ}

theorem BlockPoly.prod_cb (b : Fin (D + 1)) (μ : K) (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) :
    (s.prod fun t e => cb b μ t ^ e) = μ ^ bdeg b s := by sorry
