-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_smul_right
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hB_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:15.849722+00:00
-- url     : https://prove2.me/theorems/ac401333-4d88-41fd-ac91-122e61586365
-- title:
--   S4aux: h B smul right
-- statement:
--   The S4aux construction uses the h B smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3930-L3933
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3930-L3933

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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

theorem Formalism.HermitianLatticeCounting.P.S4aux.hB_smul_right (c : L) (x y : Fin n → L) :
    hB K Ph x (c • y) = c ^ Fintype.card K * hB K Ph x y := by sorry
