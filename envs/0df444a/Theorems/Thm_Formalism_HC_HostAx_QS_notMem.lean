-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_QS_notMem
-- name    : Formalism.HC.HostAx.QS_notMem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:56:19.814157+00:00
-- url     : https://prove2.me/theorems/23e7c8aa-5e4a-4874-a536-2d0e4a6018e0
-- title:
--   Host Ax: QS not Mem
-- statement:
--   The Host Ax construction uses the QS not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/SmallRam.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/SmallRam.lean#L42-L53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)

theorem Formalism.HC.HostAx.QS_notMem (hE : H.toHostRaw.Exact) (P : HeightOneSpectrum (𝓞 H.E)) {p : ℕ} (hp : p.Prime)
    (hc : Nat.card (𝓞 H.E ⧸ P.asIdeal) = p) (h2 : (p : 𝓞 H.E) ∉ P.asIdeal ^ 2) : (H.QS : 𝓞 H.E) ∉ P.asIdeal := by sorry
