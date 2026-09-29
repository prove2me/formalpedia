-- Prove2me | solution 1 for mme_schonhage_pan_sidePoly_coeff_eleven_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:06:12.925273+00:00
-- url     : https://prove2.me/submissions/8a5a41df-1ac9-4900-af94-696c739d41f8

import Definitions.Def_mme_schonhage_pan_certificate

open BigOperators Finset Polynomial

universe u


namespace PanLowCoeffEleven

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

variable {K : Type u} [Field K]

open PanLeanBridge

private lemma coeff_mul_range (f g : K[X]) (n : ℕ) :
    (f * g).coeff n = ∑ k ∈ Finset.range n.succ, f.coeff k * g.coeff (n - k) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private lemma p3_eleven (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    (p3 (K := K) q0 q1 q2 s i k).coeff 11 =
      uc q0 s k * wc q1 s i * bc q2 s k := by
  simp [p3, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p4_eleven (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : (p4 (K := K) q0 q1 q2 s i).coeff 11 = 0 := by
  simp [p4, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p5_eleven (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (i : Fin 5) : (p5 (K := K) q0 q1 q2 s i).coeff 11 = 0 := by
  simp [p5, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p6_eleven (q0 : Var0) (q1 : Var1) (q2 : Var2)
    (s : Fin 2) (k : Fin 11) :
    (p6 (K := K) q0 q1 q2 s k).coeff 11 =
      -(uc q0 s k * (∑ i : Fin 5, wc q1 s i) * bc q2 s k) := by
  simp [p6, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p7_eleven (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p7 (K := K) q0 q1 q2 s).coeff 11 = 0 := by
  simp [p7, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

private lemma p8_eleven (q0 : Var0) (q1 : Var1) (q2 : Var2) (s : Fin 2) :
    (p8 (K := K) q0 q1 q2 s).coeff 11 = 0 := by
  simp [p8, mon, coeff_mul_range, Finset.sum_range_succ, Polynomial.coeff_monomial]

end PanLowCoeffEleven


theorem solution
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) (s : Fin 2) :
    (PanLeanBridge.sidePoly (K := K) q0 q1 q2 s).coeff 11 = 0 := by
  open PanLeanBridge PanLowCoeffEleven in
    simp only [sidePoly, Polynomial.coeff_add, Polynomial.finset_sum_coeff,
      p3_eleven, p4_eleven, p5_eleven, p6_eleven, p7_eleven, p8_eleven,
      Finset.sum_const_zero, add_zero]
  have hmain : ((∑ i : Fin 5, ∑ k : Fin 11,
      PanLeanBridge.uc q0 s k * PanLeanBridge.wc q1 s i *
        PanLeanBridge.bc q2 s k) : K) =
      ((∑ k : Fin 11, PanLeanBridge.uc q0 s k *
        (∑ i : Fin 5, PanLeanBridge.wc q1 s i) *
        PanLeanBridge.bc q2 s k) : K) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [hmain, Finset.sum_neg_distrib]
  ring
