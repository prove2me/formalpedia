-- Prove2me | Theorems.Thm_BlockPoly_cb_ne_zero
-- name    : BlockPoly.cb_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:18.053986+00:00
-- url     : https://prove2.me/theorems/11ef7d55-338b-448b-96bf-deb2cd8f85a9
-- title:
--   Block Poly: cb ne zero
-- statement:
--   The Block Poly construction uses the cb ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L85-L90

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

theorem BlockPoly.cb_ne_zero {μ : K} (hμ : μ ≠ 0) (b : Fin (D + 1)) (t : Fin (D + 1) × Fin (N + 1)) :
    cb b μ t ≠ 0 := by sorry
