-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_two_mul_notMem_of_condN
-- name    : Formalism.HC.HostAx.two_mul_notMem_of_condN
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:39.219306+00:00
-- url     : https://prove2.me/theorems/92806ec3-d851-4dd3-83d1-65be4115fcec
-- title:
--   Host Ax: two mul not Mem of cond N
-- statement:
--   The Host Ax construction uses the two mul not Mem of cond N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/SmallRam.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/SmallRam.lean#L69-L77

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

theorem Formalism.HC.HostAx.two_mul_notMem_of_condN (P : HeightOneSpectrum (𝓞 H.E)) {T : ℕ}
    (h : ((H.condN * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal) : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal := by sorry
