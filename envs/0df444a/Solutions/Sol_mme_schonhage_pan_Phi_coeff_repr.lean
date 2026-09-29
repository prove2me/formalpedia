-- Prove2me | solution 1 for mme_schonhage_pan_Phi_coeff_repr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:01:52.805962+00:00
-- url     : https://prove2.me/submissions/169217c2-6e77-47fa-916a-614d5df46941

import Definitions.Def_mme_schonhage_pan_certificate

open MME PiTensorProduct BigOperators Finset Polynomial

universe u

namespace PanLeanBridge

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

variable {K : Type u} [Field K]

noncomputable section

private lemma slotPoly_hs3 (s : Fin 2) (i : Fin 5) (k : Fin 11)
    (q0 : Var0) (q1 : Var1) (q2 : Var2) :
    slotPoly (K := K) (s, hs3 i k) q0 q1 q2 = p3 q0 q1 q2 s i k := by
  rfl

private lemma slotPoly_hs4 (s : Fin 2) (i : Fin 5)
    (q0 : Var0) (q1 : Var1) (q2 : Var2) :
    slotPoly (K := K) (s, hs4 i) q0 q1 q2 = p4 q0 q1 q2 s i := by
  rfl

private lemma slotPoly_hs5 (s : Fin 2) (i : Fin 5)
    (q0 : Var0) (q1 : Var1) (q2 : Var2) :
    slotPoly (K := K) (s, hs5 i) q0 q1 q2 = p5 q0 q1 q2 s i := by
  rfl

private lemma slotPoly_hs6 (s : Fin 2) (k : Fin 11)
    (q0 : Var0) (q1 : Var1) (q2 : Var2) :
    slotPoly (K := K) (s, hs6 k) q0 q1 q2 = p6 q0 q1 q2 s k := by
  rfl

private lemma slotPoly_hs7 (s : Fin 2) (q0 : Var0) (q1 : Var1) (q2 : Var2) :
    slotPoly (K := K) (s, hs7) q0 q1 q2 = p7 q0 q1 q2 s := by
  rfl

private lemma slotPoly_hs8 (s : Fin 2) (q0 : Var0) (q1 : Var1) (q2 : Var2) :
    slotPoly (K := K) (s, hs8) q0 q1 q2 = p8 q0 q1 q2 s := by
  rfl

private lemma halfSlot_sum (s : Fin 2) (q0 : Var0) (q1 : Var1) (q2 : Var2) :
    (∑ h : HalfSlot, slotPoly (K := K) (s, h) q0 q1 q2) =
      sidePoly q0 q1 q2 s := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_one,
    slotPoly_hs3, slotPoly_hs4, slotPoly_hs5, slotPoly_hs6, slotPoly_hs7,
    slotPoly_hs8, hs3, hs4, hs5, hs6, hs7, hs8, sidePoly]
  ac_rfl

private lemma sum_slotPoly (q0 : Var0) (q1 : Var1) (q2 : Var2) :
    (∑ slot : Slot, slotPoly (K := K) slot q0 q1 q2) = fullPoly q0 q1 q2 := by
  rw [Fintype.sum_prod_type]
  simp only [halfSlot_sum, fullPoly]

private lemma liftFactor_repr (r : Fin 3) (f : Var r → K[X]) (n : ℕ) (q : Var r) :
    (modeBasis (K := K) r).repr (liftFactor (K := K) r f n) q = (f q).coeff n := by
  classical
  simp [liftFactor, Polynomial.coeff, Finsupp.single_apply, eq_comm]

private lemma vfun_repr (j : Fin 156) (r : Fin 3) (n : ℕ) (q : Var r) :
    (modeBasis (K := K) r).repr (vfun (K := K) j r n) q =
      (factorPoly (K := K) (slotEquiv.symm j) r q).coeff n := by
  exact liftFactor_repr r _ n q

private lemma vlin_single (r : Fin 3) (n : ℕ) (j : Fin 156) :
    vlin (K := K) r n (Pi.single j 1) = (vfun j r) n := by
  show (Pi.basisFun K (Fin 156)).constr K (fun j' => (vfun j' r) n) (Pi.single j 1) = _
  rw [show (Pi.single j (1 : K) : Fin 156 → K) = (Pi.basisFun K (Fin 156)) j from
    (Pi.basisFun_apply K (Fin 156) j).symm]
  exact Module.Basis.constr_basis (Pi.basisFun K (Fin 156)) K _ j

private lemma map_diagObj_t {d r : ℕ} {W : Fin d → Type u}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (A : ∀ i, (Fin r → K) →ₗ[K] W i) :
    PiTensorProduct.map A (TensorObj.diagObj K d r).t =
      ∑ j : Fin r, tprod K (fun i => A i (Pi.single j 1)) := by
  change PiTensorProduct.map A
      (∑ j : Fin r, tprod K (fun (_ : Fin d) => (Pi.single j 1 : Fin r → K))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [PiTensorProduct.map_tprod]

private lemma Phi_A_single (m : Fin 3 → ℕ) (j : Fin 156) (s : Fin 3) :
    (Phi (K := K)).A s (m s) (Pi.single j 1) = (vfun j s) (m s) := by
  change vlin s (m s) (Pi.single j 1) = _
  exact vlin_single s (m s) j

private lemma Phi_map_diag_tprod (m : Fin 3 → ℕ) :
    PiTensorProduct.map (fun s => (Phi (K := K)).A s (m s))
        (TensorObj.diagObj K 3 156).t =
      ∑ j : Fin 156, tprod K (fun s => (vfun j s) (m s)) := by
  calc
    _ = ∑ j : Fin 156, tprod K
          (fun s => (Phi (K := K)).A s (m s) (Pi.single j 1)) :=
      map_diagObj_t (K := K) (A := fun s => (Phi (K := K)).A s (m s))
    _ = _ := by simp_rw [Phi_A_single]

private lemma Phi_coeff_expand (n : ℕ) :
    (Phi (K := K)).coeff n = ∑ j : Fin 156,
      (Finset.Nat.antidiagonalTuple 3 n).sum
        (fun m => tprod K (fun r => (vfun j r) (m r))) := by
  unfold PolyFamily.coeff
  simp_rw [Phi_map_diag_tprod]
  rw [Finset.sum_comm]

private lemma tensorBasis_tprod_repr (x : ∀ r, (Xobj (K := K)).V r)
    (q : (r : Fin 3) → Var r) :
    (tensorBasis (K := K)).repr (tprod K x) q =
      ∏ r, (modeBasis (K := K) r).repr (x r) (q r) := by
  exact Basis.piTensorProduct_repr_tprod_apply _ _ _

private lemma coeff_three (f0 f1 f2 : K[X]) (n : ℕ) :
    (Finset.Nat.antidiagonalTuple 3 n).sum
        (fun m => f0.coeff (m 0) * f1.coeff (m 1) * f2.coeff (m 2)) =
      (f0 * f1 * f2).coeff n := by
  rw [mul_assoc, Polynomial.coeff_mul]
  simp_rw [Polynomial.coeff_mul]
  change (List.map
      (fun m : Fin 3 → ℕ => f0.coeff (m 0) * f1.coeff (m 1) * f2.coeff (m 2))
      (List.Nat.antidiagonalTuple 3 n)).sum =
    (List.map (fun x => f0.coeff x.1 *
      (List.map (fun i => f1.coeff i.1 * f2.coeff i.2)
        (List.Nat.antidiagonal x.2)).sum) (List.Nat.antidiagonal n)).sum
  have hcons (a b c : ℕ) :
      @Fin.cons 2 (fun _ : Fin 3 => ℕ) a (![b, c] : Fin 2 → ℕ) (2 : Fin 3) = c := by
    rfl
  have hinner (a : K) (l : List (ℕ × ℕ)) :
      (l.map (fun i => a * (f1.coeff i.1 * f2.coeff i.2))).sum =
        a * (l.map (fun i => f1.coeff i.1 * f2.coeff i.2)).sum := by
    induction l with
    | nil => simp
    | cons x xs ih => simp [ih, mul_add]
  rw [List.Nat.antidiagonalTuple]
  simp_rw [List.Nat.antidiagonalTuple_two]
  simp [List.flatMap, List.sum_flatten, Function.comp_def, hcons, mul_assoc, hinner]

private lemma phi_coeff_repr_internal (n : ℕ) (q : ∀ r : Fin 3, Var r) :
    (tensorBasis (K := K)).repr ((Phi (K := K)).coeff n) q =
      (fullPoly (K := K) (q 0) (q 1) (q 2)).coeff n := by
  have hcoord :
      (tensorBasis (K := K)).repr
          (∑ j : Fin 156, (Finset.Nat.antidiagonalTuple 3 n).sum
            (fun m => tprod K (fun r => (vfun j r) (m r)))) q =
        ∑ j : Fin 156, (Finset.Nat.antidiagonalTuple 3 n).sum
          (fun m => ∏ r,
            (modeBasis (K := K) r).repr ((vfun j r) (m r)) (q r)) := by
    rw [map_sum (tensorBasis (K := K)).repr]
    rw [Finset.sum_apply']
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_sum (tensorBasis (K := K)).repr]
    rw [Finset.sum_apply']
    refine Finset.sum_congr rfl (fun m _ => ?_)
    exact tensorBasis_tprod_repr _ q
  rw [Phi_coeff_expand, hcoord]
  simp only [Fin.prod_univ_three]
  simp_rw [vfun_repr]
  rw [show (∑ j : Fin 156,
      ∑ m ∈ Finset.Nat.antidiagonalTuple 3 n,
        (factorPoly (K := K) (slotEquiv.symm j) 0 (q 0)).coeff (m 0) *
        (factorPoly (K := K) (slotEquiv.symm j) 1 (q 1)).coeff (m 1) *
        (factorPoly (K := K) (slotEquiv.symm j) 2 (q 2)).coeff (m 2)) =
      ∑ j : Fin 156, (slotPoly (K := K) (slotEquiv.symm j) (q 0) (q 1) (q 2)).coeff n
    from Finset.sum_congr rfl fun j _ => coeff_three _ _ _ n]
  rw [← Equiv.sum_comp slotEquiv]
  simp only [Equiv.symm_apply_apply]
  rw [← Polynomial.finset_sum_coeff]
  exact congrArg (fun p : K[X] => p.coeff n) (sum_slotPoly (q 0) (q 1) (q 2))

end

end PanLeanBridge

theorem solution {K : Type u} [Field K] (n : ℕ)
    (q : ∀ r : Fin 3, PanLeanBridge.Var r) :
    (PanLeanBridge.tensorBasis (K := K)).repr
        ((PanLeanBridge.Phi (K := K)).coeff n) q =
      (PanLeanBridge.fullPoly (K := K) (q 0) (q 1) (q 2)).coeff n := by
  exact PanLeanBridge.phi_coeff_repr_internal n q
