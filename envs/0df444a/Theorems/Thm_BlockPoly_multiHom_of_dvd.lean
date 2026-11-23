-- Prove2me | Theorems.Thm_BlockPoly_multiHom_of_dvd
-- name    : BlockPoly.multiHom_of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:56.146356+00:00
-- url     : https://prove2.me/theorems/8d48d2dc-254d-4dbd-9798-bf94b4905dec
-- title:
--   Block Poly: multi Hom of dvd
-- statement:
--   The Block Poly construction uses the multi Hom of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L216-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L216-L254

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

theorem BlockPoly.multiHom_of_dvd [CharZero K] {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hsc : ∀ b, g ∣ diag (cb b (2 : K)) g)
    (hsw : ∀ e : Equiv.Perm (Fin (D + 1)), e 0 = 0 → g ∣ rename (eT e) g)
    (htr : ∀ a, g ∣ transl a g) (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) (hs : s ∈ g.support)
    (b : Fin (D + 1)) :
    ∑ j, s (b, j) = if b = 0 then 0 else g.support.sup fun r => ∑ j, r (1, j) := by sorry
