-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_uniq
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.unram_uniq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:46.131793+00:00
-- url     : https://prove2.me/theorems/26eceba4-d2ff-401b-878f-bbe02db076a9
-- title:
--   S4aux: unram uniq
-- statement:
--   The S4aux construction uses the unram uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1240-L1250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1240-L1250

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.unram_uniq (hU : Unram o O) (c : O) (hc : ∀ a : O, a * c + star (a * c) = 0) : c = 0 := by sorry
