-- Prove2me | Theorems.Thm_BlockPoly_bdeg_eq_of_dvd
-- name    : BlockPoly.bdeg_eq_of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:44.068935+00:00
-- url     : https://prove2.me/theorems/d64adce0-f01f-44ac-997a-9d88473ffa4d
-- title:
--   Block Poly: bdeg eq of dvd
-- statement:
--   The Block Poly construction uses the bdeg eq of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L100-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L100-L122

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

theorem BlockPoly.bdeg_eq_of_dvd [CharZero K] (b : Fin (D + 1))
    {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : g ∣ diag (cb b (2 : K)) g) {s s' : Fin (D + 1) × Fin (N + 1) →₀ ℕ}
    (hs : s ∈ g.support) (hs' : s' ∈ g.support) : bdeg b s = bdeg b s' := by sorry
