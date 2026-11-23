-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_sgn
-- name    : Formalism.HermitianLatticesTheory.majDual_sgn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:35.36816+00:00
-- url     : https://prove2.me/theorems/3ce40aa5-ffe8-41d2-a2b0-fb4a2cb3d168
-- title:
--   Hermitian Lattices Theory: maj Dual sgn
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L71-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L71-L86

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HermitianLatticesTheory.majDual_sgn (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsFrame h b v (X v)) (v : InfinitePlace K) :
    (X v).conjTranspose * gramAt h b v * X v =
      Matrix.diagonal (fun i => ((sgnAt h b X v i : ℝ) : ℂ)) ∧
      ∀ i, sgnAt h b X v i = 1 ∨ sgnAt h b X v i = -1 := by sorry
