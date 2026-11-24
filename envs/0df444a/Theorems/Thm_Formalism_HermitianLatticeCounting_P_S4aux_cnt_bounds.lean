-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_cnt_bounds
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.cnt_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:04.460641+00:00
-- url     : https://prove2.me/theorems/1de48ac4-c750-43c0-8b9f-0db0ff722d5d
-- title:
--   S4aux: cnt bounds
-- statement:
--   The S4aux construction uses the cnt bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3006-L3085
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3006-L3085

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.cnt_bounds (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) (j : ℕ) : 2 * j + 3 ≤ n →
    ∀ G : Matrix (Fin j) (Fin j) L, (∀ a b, G b a = G a b ^ Fintype.card K) →
    (1 - ((Fintype.card K : ℝ) ^ 2) ^ j / (Fintype.card K : ℝ) ^ n) *
        ((Fintype.card K : ℝ) ^ (2 * n * j) / (Fintype.card K : ℝ) ^ (j ^ 2))
      ≤ ((univ.filter fun X : Fin j → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card : ℝ) ∧
    ((univ.filter fun X : Fin j → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card : ℝ)
      ≤ (1 + ((Fintype.card K : ℝ) ^ 2) ^ j / (Fintype.card K : ℝ) ^ n) *
        ((Fintype.card K : ℝ) ^ (2 * n * j) / (Fintype.card K : ℝ) ^ (j ^ 2)) := by sorry
