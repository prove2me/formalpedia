-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hMat_li
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hMat_li
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:30.338041+00:00
-- url     : https://prove2.me/theorems/d5f6ee63-127d-4062-b263-39024b5bea54
-- title:
--   S4aux: h Mat li
-- statement:
--   The S4aux construction uses the h Mat li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2703-L2728
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2703-L2728

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.hMat_li (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) : LinearIndependent L (hMat K Ph X).row := by sorry
