-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_zdual
-- name    : Formalism.HermitianLatticesTheory.majDual_zdual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:06.225149+00:00
-- url     : https://prove2.me/theorems/28adeb38-21b3-4cbc-acd8-c4ec13495c12
-- title:
--   Hermitian Lattices Theory: maj Dual zdual
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual zdual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L317-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L317-L428

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
variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

theorem Formalism.HermitianLatticesTheory.majDual_zdual [IsTotallyComplex K] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hX : ∀ v, IsFrame h b v (X v)) (L : Submodule (RingOfIntegers K) V)
    [DiscreteTopology (zmap (realize b X) L)] [IsZLattice ℝ (zmap (realize b X) L)]
    (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    w ∈ Formalism.HadamardInequality.zdual (zmap (realize b X) L) ↔
      ∃ y : V, (∀ x ∈ L, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = 2 * z) ∧
        w = jW h b X (realize b X y) := by sorry
