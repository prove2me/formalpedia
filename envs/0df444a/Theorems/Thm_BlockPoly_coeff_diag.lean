-- Prove2me | Theorems.Thm_BlockPoly_coeff_diag
-- name    : BlockPoly.coeff_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:09.580472+00:00
-- url     : https://prove2.me/theorems/7dcdf1ff-bd3d-4a2c-806f-6bcd28164de0
-- title:
--   Block Poly: coeff diag
-- statement:
--   The Block Poly construction uses the coeff diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L25-L35

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

theorem BlockPoly.coeff_diag (c : σ → K) (g : MvPolynomial σ K) (s : σ →₀ ℕ) :
    coeff s (diag c g) = (s.prod fun t e => c t ^ e) * coeff s g := by sorry
