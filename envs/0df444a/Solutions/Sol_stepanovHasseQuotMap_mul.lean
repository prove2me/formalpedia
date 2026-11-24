-- Prove2me | solution 1 for stepanovHasseQuotMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T15:51:18.034836+00:00
-- url     : https://prove2.me/submissions/4807e476-244c-4023-b1d3-4dae0b705bc3

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovSystem
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring




theorem solution
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p * f ^ (r - k) =
      hasseDerivOp F k (p * f ^ r) :=
by
  set g : Polynomial F := f ^ (r - k) with hgdef
  set numMap : Polynomial F →ₗ[F] Polynomial F :=
    (Polynomial.hasseDeriv k).comp (polyMulRightLinear (F := F) (f ^ r)) with hnumMap
  have hmem : ∀ p, numMap p ∈ LinearMap.range (polyMulRightLinear (F := F) g) := by
    intro p
    rcases hasseDerivOp_mul_pow_dvd F k r p f with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simpa [numMap, g, hasseDerivOp, polyMulRightLinear, mul_comm] using hq.symm
  set z : LinearMap.range (polyMulRightLinear (F := F) g) :=
    LinearMap.codRestrict (LinearMap.range (polyMulRightLinear (F := F) g)) numMap hmem p
      with hz
  calc
    stepanovHasseQuotMap (F := F) (f := f) hf r k p * f ^ (r - k)
        = polyMulRightLinear (F := F) g
            (polyDivRightLinear (F := F) (g := g) (pow_ne_zero _ hf) z) := by
          rfl
    _ = z := by
          exact congrArg Subtype.val
            ((LinearEquiv.ofInjective (polyMulRightLinear (F := F) g)
              (fun _ _ => mul_right_cancel₀ (pow_ne_zero _ hf))).apply_symm_apply z)
    _ = numMap p := rfl
    _ = hasseDerivOp F k (p * f ^ r) := by
      simp [numMap, polyMulRightLinear, LinearMap.comp_apply, hasseDerivOp]
