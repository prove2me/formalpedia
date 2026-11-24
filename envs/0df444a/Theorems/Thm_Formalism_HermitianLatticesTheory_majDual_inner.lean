-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_inner
-- name    : Formalism.HermitianLatticesTheory.majDual_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:19.021802+00:00
-- url     : https://prove2.me/theorems/3ce45906-7a16-4030-ab64-c33b62faffdc
-- title:
--   Hermitian Lattices Theory: maj Dual inner
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L109-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L109-L121

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

theorem Formalism.HermitianLatticesTheory.majDual_inner [IsTotallyComplex K] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hX : ∀ v, IsFrame h b v (X v)) (x y : V) :
    inner ℝ (realize b X x) (jW h b X (realize b X y)) =
      ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ) / 2 := by sorry
