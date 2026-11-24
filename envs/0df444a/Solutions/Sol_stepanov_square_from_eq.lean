-- Prove2me | solution 1 for stepanov_square_from_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:19:19.374429+00:00
-- url     : https://prove2.me/submissions/ade06848-f62c-4d9d-8185-a62764692903

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




theorem solution (F : Type*) [Field F]
    (f : Polynomial F) (r s : Polynomial F) (f₀ : F)
    (hf₀_ne_zero : f₀ ≠ 0) (hs_ne_zero : s ≠ 0)
    (heq : r * r * f = s * s * Polynomial.C f₀) :
    ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f :=
by
  let K := AlgebraicClosure F
  let fK := Polynomial.map (algebraMap F K) f
  let rK := Polynomial.map (algebraMap F K) r
  let sK := Polynomial.map (algebraMap F K) s
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_eq_mul_self (k := K) (algebraMap F K f₀)
  let L := FractionRing (Polynomial K)
  have heqK :
      rK * rK * fK = sK * sK * Polynomial.C (algebraMap F K f₀) := by
    simpa [fK, rK, sK, Polynomial.map_mul, Polynomial.map_C] using
      congrArg (Polynomial.map (algebraMap F K)) heq
  have hrK_ne : rK ≠ 0 := by
    intro hr0
    have h0 : sK * sK * Polynomial.C (algebraMap F K f₀) = 0 := by
      calc
        sK * sK * Polynomial.C (algebraMap F K f₀)
            = rK * rK * fK := heqK.symm
        _ = 0 := by simp [hr0]
    have hsK_ne : sK ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap F K).injective).2 hs_ne_zero
    have hCf0_ne : Polynomial.C (algebraMap F K f₀) ≠ 0 := by
      simp [hf₀_ne_zero]
    exact (mul_ne_zero (mul_ne_zero hsK_ne hsK_ne) hCf0_ne) h0
  let g : L :=
    algebraMap (Polynomial K) L sK / algebraMap (Polynomial K) L rK *
      algebraMap (Polynomial K) L (Polynomial.C α)
  have hrK_ne_alg : algebraMap (Polynomial K) L rK ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff (R := Polynomial K) (K := L)
          (x := rK)).not.mpr hrK_ne
  have hCα_sq : Polynomial.C α * Polynomial.C α =
      Polynomial.C (algebraMap F K f₀) := by
    rw [← Polynomial.C_mul, ← hα]
  have hg_sq : g * g = algebraMap (Polynomial K) L fK := by
    simp only [g]
    calc
      algebraMap (Polynomial K) L sK / algebraMap (Polynomial K) L rK *
              algebraMap (Polynomial K) L (Polynomial.C α) *
            (algebraMap (Polynomial K) L sK / algebraMap (Polynomial K) L rK *
              algebraMap (Polynomial K) L (Polynomial.C α))
          =
            (algebraMap (Polynomial K) L sK *
                  algebraMap (Polynomial K) L (Polynomial.C α) /
                algebraMap (Polynomial K) L rK) *
              (algebraMap (Polynomial K) L sK *
                  algebraMap (Polynomial K) L (Polynomial.C α) /
                algebraMap (Polynomial K) L rK) := by
              ring
      _ =
            (algebraMap (Polynomial K) L sK *
                algebraMap (Polynomial K) L (Polynomial.C α)) *
              (algebraMap (Polynomial K) L sK *
                algebraMap (Polynomial K) L (Polynomial.C α)) /
              (algebraMap (Polynomial K) L rK *
                algebraMap (Polynomial K) L rK) := by
              rw [div_mul_div_comm]
      _ =
            algebraMap (Polynomial K) L
                (sK * Polynomial.C α * (sK * Polynomial.C α)) /
              algebraMap (Polynomial K) L (rK * rK) := by
              simp only [← map_mul]
      _ =
            algebraMap (Polynomial K) L (rK * rK * fK) /
              algebraMap (Polynomial K) L (rK * rK) := by
              congr 2
              calc
                sK * Polynomial.C α * (sK * Polynomial.C α)
                    = sK * sK * (Polynomial.C α * Polynomial.C α) := by
                      ring
                _ = rK * rK * fK := by
                      rw [hCα_sq, heqK.symm]
      _ = algebraMap (Polynomial K) L fK := by
              rw [map_mul, mul_comm, mul_div_assoc,
                div_self (by
                  rw [map_mul]
                  exact mul_ne_zero hrK_ne_alg hrK_ne_alg),
                mul_one]
  obtain ⟨h, hh⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral <|
      IsIntegral.of_pow (by norm_num)
        ((sq g ▸ hg_sq) ▸ isIntegral_algebraMap)
  refine ⟨h, ?_⟩
  refine IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K)) ?_
  rw [map_mul, hh, hg_sq]
