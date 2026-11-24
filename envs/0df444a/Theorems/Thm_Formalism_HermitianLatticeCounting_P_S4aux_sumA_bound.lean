-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_sumA_bound
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.sumA_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:41.14337+00:00
-- url     : https://prove2.me/theorems/ee23f1d3-0c59-4a21-8a60-b0c22aec41b3
-- title:
--   S4aux: sum A bound
-- statement:
--   The S4aux construction uses the sum A bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2737-L2783
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2737-L2783

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.sumA_bound (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (g : Fin j → L) (bq : (Fin n → L) → K) (hbq : ∀ x, algebraMap K L (bq x) = hB K Ph x x)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) :
    ‖∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x)‖
      ≤ (Fintype.card K : ℝ) ^ n := by sorry
