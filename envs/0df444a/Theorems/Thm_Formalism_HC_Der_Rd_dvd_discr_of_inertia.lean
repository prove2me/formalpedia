-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_dvd_discr_of_inertia
-- name    : Formalism.HC.Der.Rd.dvd_discr_of_inertia
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:59.118082+00:00
-- url     : https://prove2.me/theorems/0fcb62c4-01a5-4a01-8e9f-dfa5ae842be6
-- title:
--   Rd: dvd discr of inertia
-- statement:
--   The Rd construction uses the dvd discr of inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/DvdDiscrOfInertia.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/DvdDiscrOfInertia.lean#L31-L50

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd

theorem Formalism.HC.Der.Rd.dvd_discr_of_inertia {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})],
      ∃ σ : E ≃ₐ[ℚ] E, σ ≠ 1 ∧ ∀ x : 𝓞 E, σ • x - x ∈ P) : (l : ℤ) ∣ discr E := by sorry
