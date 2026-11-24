-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_cnt_succ
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.cnt_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:06.7858+00:00
-- url     : https://prove2.me/theorems/a911b4e7-1d81-47d2-a934-3ebd05037059
-- title:
--   S4aux: cnt succ
-- statement:
--   The S4aux construction uses the cnt succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2969-L3003
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2969-L3003

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.cnt_succ (h2 : Module.finrank K L = 2) (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K)
    (j : ℕ) (G : Matrix (Fin (j + 1)) (Fin (j + 1)) L) (hG : ∀ a b, G b a = G a b ^ Fintype.card K) :
    (univ.filter fun X : Fin (j + 1) → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card
      = ∑ X' ∈ univ.filter (fun X' : Fin j → Fin n → L => LinearIndependent L X' ∧
          ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ),
        (univ.filter fun x : Fin n → L => x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0).card := by sorry
