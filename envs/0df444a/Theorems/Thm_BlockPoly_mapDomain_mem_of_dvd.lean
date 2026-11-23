-- Prove2me | Theorems.Thm_BlockPoly_mapDomain_mem_of_dvd
-- name    : BlockPoly.mapDomain_mem_of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:51.41724+00:00
-- url     : https://prove2.me/theorems/a6086ce2-daef-4d56-ac88-a88ab6bc2521
-- title:
--   Block Poly: map Domain mem of dvd
-- statement:
--   The Block Poly construction uses the map Domain mem of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L135-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L135-L160

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

theorem BlockPoly.mapDomain_mem_of_dvd (e : Equiv.Perm (Fin (D + 1)))
    {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : g ∣ rename (eT e) g) {s : Fin (D + 1) × Fin (N + 1) →₀ ℕ} (hs : s ∈ g.support) :
    s.mapDomain (eT e) ∈ g.support := by sorry
