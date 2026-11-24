-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_mulVec
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hB_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:22.284791+00:00
-- url     : https://prove2.me/theorems/443dcb93-ffe9-41f5-989e-91c4819d51c4
-- title:
--   S4aux: h B mul Vec
-- statement:
--   The S4aux construction uses the h B mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2698-L2701
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2698-L2701

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
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

theorem Formalism.HermitianLatticeCounting.P.S4aux.hB_mulVec {j : ℕ} (X : Fin j → Fin n → L) (x : Fin n → L) (b : Fin j) :
    hB K Ph x (X b) = (hMat K Ph X).mulVec x b := by sorry
