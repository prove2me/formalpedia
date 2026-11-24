-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_step_Z
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.step_Z
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:35.847794+00:00
-- url     : https://prove2.me/theorems/91173d31-58a4-4407-958e-708b02b49b24
-- title:
--   S4aux: step Z
-- statement:
--   The S4aux construction uses the step Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2786-L2857
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2786-L2857

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
open scoped Classical

theorem Formalism.HermitianLatticeCounting.P.S4aux.step_Z (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) (g : Fin j → L) (a : L) (ha : a ^ Fintype.card K = a) (c : ℕ)
    (hc : c * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ n) :
    |(Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L =>
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) - c|
      ≤ (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n := by sorry
