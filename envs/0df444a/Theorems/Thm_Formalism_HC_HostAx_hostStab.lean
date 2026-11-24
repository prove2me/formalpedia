-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_hostStab
-- name    : Formalism.HC.HostAx.hostStab
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:54:50.675972+00:00
-- url     : https://prove2.me/theorems/983a00c2-5934-47cf-863d-cb7f502db87a
-- title:
--   Host Ax: host Stab
-- statement:
--   The Host Ax construction uses the host Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L346-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L346-L367

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_hostStab

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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)

theorem Formalism.HC.HostAx.hostStab (k g : ℕ) (hg : g.Prime) (hlt : 4 * φ.ord * k < g - 1)
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin k) H.E)) (hΓ : ∀ γ ∈ Γ, ∃ m : ℕ, orderOf γ = g ^ m) : Γ = ⊥ := by sorry
