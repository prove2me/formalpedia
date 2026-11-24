-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_mem_mO_of_trace
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.mem_mO_of_trace
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:15.047009+00:00
-- url     : https://prove2.me/theorems/b983fdc3-e9f2-449e-89e3-0d9de4147354
-- title:
--   S4aux: mem m O of trace
-- statement:
--   The S4aux construction uses the mem m O of trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3204-L3216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3204-L3216

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

theorem Formalism.HermitianLatticeCounting.P.S4aux.mem_mO_of_trace (hU : Unram o O) (T : O →ₗ[o] o) (hT : ∀ a, algebraMap o O (T a) = a + star a)
    (z : O) (hz : ∀ s, T (s * z) ∈ IsLocalRing.maximalIdeal o) : z ∈ mO o O := by sorry
