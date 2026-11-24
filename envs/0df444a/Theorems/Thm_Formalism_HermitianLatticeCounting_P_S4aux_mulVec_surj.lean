-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_mulVec_surj
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.mulVec_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:55.977741+00:00
-- url     : https://prove2.me/theorems/51035092-f7ba-4f5f-8dac-2b3be5f9412a
-- title:
--   S4aux: mul Vec surj
-- statement:
--   The S4aux construction uses the mul Vec surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2321-L2330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2321-L2330

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
variable {F : Type} [Field F] [Fintype F]

theorem Formalism.HermitianLatticeCounting.P.S4aux.mulVec_surj {j n : ℕ} (M : Matrix (Fin j) (Fin n) F) (hM : LinearIndependent F M.row) :
    Function.Surjective M.mulVec := by sorry
