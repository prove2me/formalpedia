-- Prove2me | solution 1 for mme_schonhage_pan_fullPoly_coeff_ten_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:06:12.347012+00:00
-- url     : https://prove2.me/submissions/94dc4587-7240-483f-af59-fef70b25aa22

import Definitions.Def_mme_schonhage_pan_certificate

open BigOperators Finset Polynomial

universe u


namespace PanLowCoeffTen

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

variable {K : Type u} [Field K]

open PanLeanBridge

private lemma coeff_mul_range (f g : K[X]) (n : ℕ) :
    (f * g).coeff n = ∑ k ∈ Finset.range n.succ, f.coeff k * g.coeff (n - k) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private lemma p3_ten (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    (p3 (K := K) q0 q1 q2 s i k).coeff 10 =
      ac q0 s i * zc q1 k * vc q2 k i +
      uc q0 s k * zc q1 k * yc q2 s i +
      xc q0 s k i * wc q1 s i * yc q2 s i := by
  simp [p3, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]
  ring

private lemma p4_ten (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : (p4 (K := K) q0 q1 q2 s i).coeff 10 = 0 := by
  simp [p4, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p5_ten (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) :
    (p5 (K := K) q0 q1 q2 s i).coeff 10 =
      -((∑ k : Fin 11, xc q0 s k i) * wc q1 s i * yc q2 s i) := by
  simp [p5, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p6_ten (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (k : Fin 11) :
    (p6 (K := K) q0 q1 q2 s k).coeff 10 =
      -(uc q0 s k * zc q1 k * (∑ i : Fin 5, yc q2 s i)) := by
  simp [p6, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p7_ten (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p7 (K := K) q0 q1 q2 s).coeff 10 = 0 := by
  simp [p7, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p8_ten (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p8 (K := K) q0 q1 q2 s).coeff 10 = 0 := by
  simp [p8, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma side_ten (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (sidePoly (K := K) q0 q1 q2 s).coeff 10 = residual q0 q1 q2 s := by
  simp only [sidePoly, PanLeanBridge.residual, Polynomial.coeff_add,
    Polynomial.finset_sum_coeff,
    p3_ten, p4_ten, p5_ten, p6_ten, p7_ten, p8_ten,
    Finset.sum_const_zero, add_zero]
  simp_rw [Finset.sum_add_distrib]
  have hu : ((∑ i : Fin 5, ∑ k : Fin 11,
      uc q0 s k * zc q1 k * yc q2 s i) : K) =
      ((∑ k : Fin 11, uc q0 s k * zc q1 k *
        (∑ i : Fin 5, yc q2 s i)) : K) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.mul_sum]
  have hx : ((∑ i : Fin 5, ∑ k : Fin 11,
      xc q0 s k i * wc q1 s i * yc q2 s i) : K) =
      ((∑ i : Fin 5, (∑ k : Fin 11, xc q0 s k i) *
        wc q1 s i * yc q2 s i) : K) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hu, hx]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  ring

end PanLowCoeffTen


theorem solution
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) :
    (PanLeanBridge.fullPoly (K := K) q0 q1 q2).coeff 10 = 0 := by
  have hac (i : Fin 5) :
      PanLeanBridge.ac (K := K) q0 (1 : Fin 2) i =
        -PanLeanBridge.ac q0 (0 : Fin 2) i := by
    simp [PanLeanBridge.ac, PanLeanBridge.sideSign]
  have hres : PanLeanBridge.residual (K := K) q0 q1 q2 (1 : Fin 2) =
      -PanLeanBridge.residual q0 q1 q2 (0 : Fin 2) := by
    simp only [PanLeanBridge.residual]
    simp_rw [hac, neg_mul, Finset.sum_neg_distrib]
  simp only [PanLeanBridge.fullPoly, Fin.sum_univ_two, Polynomial.coeff_add,
    PanLowCoeffTen.side_ten]
  rw [hres]
  exact add_neg_cancel _
