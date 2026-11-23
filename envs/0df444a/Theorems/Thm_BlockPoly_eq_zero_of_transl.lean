-- Prove2me | Theorems.Thm_BlockPoly_eq_zero_of_transl
-- name    : BlockPoly.eq_zero_of_transl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:08.947793+00:00
-- url     : https://prove2.me/theorems/4be3054b-00a8-48ec-9561-eeffe6f68099
-- title:
--   Block Poly: eq zero of transl
-- statement:
--   The Block Poly construction uses the eq zero of transl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L197-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L197-L214

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

theorem BlockPoly.eq_zero_of_transl [Infinite K] {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : ∀ a, g ∣ transl a g) (h0 : ∀ s ∈ g.support, 0 < bdeg 0 s) : g = 0 := by sorry
