-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_fix_thM_iff
-- name    : Formalism.HC.HostRaw.fix_thM_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:53.919489+00:00
-- url     : https://prove2.me/theorems/b2d104e6-1635-443e-90fc-1225d0f7fe81
-- title:
--   Host Raw: fix th M iff
-- statement:
--   The Host Raw construction uses the fix th M iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L95-L102

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.fix_thM_iff (m : ℕ) (σ : H.E ≃ₐ[ℚ] H.E) : σ (H.thM m) = H.thM m ↔ σ ∈ H.congrGal m := by sorry
