-- Prove2me | Theorems.Thm_BlockPoly_bdeg_mapDomain
-- name    : BlockPoly.bdeg_mapDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:43.7992+00:00
-- url     : https://prove2.me/theorems/275c3821-1848-4929-9233-890210ae88b9
-- title:
--   Block Poly: bdeg map Domain
-- statement:
--   The Block Poly construction uses the bdeg map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L127-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L127-L133

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

theorem BlockPoly.bdeg_mapDomain (e : Equiv.Perm (Fin (D + 1))) (b : Fin (D + 1))
    (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) :
    bdeg (e b) (s.mapDomain (eT e)) = bdeg b s := by sorry
