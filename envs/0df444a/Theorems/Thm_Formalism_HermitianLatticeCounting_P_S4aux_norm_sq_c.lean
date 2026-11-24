-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_norm_sq_c
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.norm_sq_c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:19.334803+00:00
-- url     : https://prove2.me/theorems/512f4c51-5a36-47e5-8c43-5f069cdad1b9
-- title:
--   S4aux: norm sq c
-- statement:
--   The S4aux construction uses the norm sq c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L904-L906
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L904-L906

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.norm_sq_c {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : V) :
    ((‖x‖ : ℝ) : ℂ) ^ 2 = inner ℂ x x := by sorry
