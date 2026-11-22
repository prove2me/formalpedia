-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_not_unit_of_mem_mO
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.not_unit_of_mem_mO
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:41.251871+00:00
-- url     : https://prove2.me/theorems/1a97d09d-48f3-440f-b7b2-9665ca5657c5
-- title:
--   S4aux: not unit of mem m O
-- statement:
--   The S4aux construction uses the not unit of mem m O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3198-L3202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3198-L3202

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.not_unit_of_mem_mO (hU : Unram o O) (x : O) (hx : x ∈ mO o O) : ¬ IsUnit x := by sorry
