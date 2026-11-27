-- Prove2me | solution 1 for det_polynomial_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:35.327135+00:00
-- url     : https://prove2.me/submissions/44f9d5c8-ef9a-4b51-ac8c-4708c865e299

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_DetMemSubalgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_PerpVecOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_FormPartialDerivatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem det_mem_subalgebra_of_entries_mem {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A]
    (S : Subalgebra R A) {m : ℕ} (M : Matrix (Fin m) (Fin m) A) (hM : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  let M' : Matrix (Fin m) (Fin m) S := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hMap : M = (S.val : S →+* A).mapMatrix M' := by
    ext i j
    rfl
  rw [hMap, ← RingHom.map_det]
  exact (M'.det).2
end

set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.DetPolyHarmSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.DetPolyHarmSt
  intro R _ p q n e f c c' horth a b
  classical

  obtain ⟨Ay, hAy⟩ : ∃ S : Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R),
      ∀ g, g ∈ S ↔ ∀ i, MvPolynomial.pderiv (Sum.inl i) g = 0 :=
    ⟨{ carrier := {g | ∀ i, MvPolynomial.pderiv (Sum.inl i) g = 0}
       mul_mem' := by
         intro g h hg hh i
         rw [MvPolynomial.pderiv_mul, hg i, hh i]
         ring
       one_mem' := fun i => by simp
       add_mem' := by
         intro g h hg hh i
         rw [map_add, hg i, hh i, add_zero]
       zero_mem' := fun i => by simp
       algebraMap_mem' := fun r i => by simp [MvPolynomial.algebraMap_eq] }, fun g => Iff.rfl⟩

  obtain ⟨Sx, hSx⟩ : ∃ S : Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R),
      ∀ g, g ∈ S ↔ (∀ j, MvPolynomial.pderiv (Sum.inr j) g = 0) ∧
        ∃ G : Fin p → MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R,
          ∀ k, MvPolynomial.pderiv (Sum.inl (a, k)) g = ∑ b', G b' * MvPolynomial.C (e b' k) :=
    ⟨{ carrier := {g | (∀ j, MvPolynomial.pderiv (Sum.inr j) g = 0) ∧
          ∃ G : Fin p → MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R,
            ∀ k, MvPolynomial.pderiv (Sum.inl (a, k)) g = ∑ b', G b' * MvPolynomial.C (e b' k)}
       mul_mem' := by
         rintro g h ⟨hg0, G, hG⟩ ⟨hh0, H, hH⟩
         refine ⟨fun j => by rw [MvPolynomial.pderiv_mul, hg0 j, hh0 j]; ring,
           fun b' => G b' * h + g * H b', fun k => ?_⟩
         rw [MvPolynomial.pderiv_mul, hG k, hH k, Finset.sum_mul, Finset.mul_sum,
           ← Finset.sum_add_distrib]
         refine Finset.sum_congr rfl fun b' _ => ?_
         ring
       one_mem' := ⟨fun j => by simp, fun _ => 0, fun k => by simp⟩
       add_mem' := by
         rintro g h ⟨hg0, G, hG⟩ ⟨hh0, H, hH⟩
         refine ⟨fun j => by rw [map_add, hg0 j, hh0 j, add_zero], fun b' => G b' + H b', fun k => ?_⟩
         rw [map_add, hG k, hH k, ← Finset.sum_add_distrib]
         refine Finset.sum_congr rfl fun b' _ => ?_
         ring
       zero_mem' := ⟨fun j => by simp, fun _ => 0, fun k => by simp⟩
       algebraMap_mem' := fun r => ⟨fun j => by simp [MvPolynomial.algebraMap_eq], fun _ => 0,
         fun k => by simp [MvPolynomial.algebraMap_eq]⟩ }, fun g => Iff.rfl⟩

  obtain ⟨Sy, hSy⟩ : ∃ S : Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R),
      ∀ g, g ∈ S ↔ g ∈ Ay ∧
        ∃ H : Fin q → MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R, (∀ d, H d ∈ Ay) ∧
          ∀ k, MvPolynomial.pderiv (Sum.inr (b, k)) g = ∑ d, H d * MvPolynomial.C (f d k) :=
    ⟨{ carrier := {g | g ∈ Ay ∧
          ∃ H : Fin q → MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R, (∀ d, H d ∈ Ay) ∧
            ∀ k, MvPolynomial.pderiv (Sum.inr (b, k)) g = ∑ d, H d * MvPolynomial.C (f d k)}
       mul_mem' := by
         rintro g h ⟨hgA, G, hGA, hG⟩ ⟨hhA, H, hHA, hH⟩
         refine ⟨Ay.mul_mem hgA hhA, fun d => G d * h + g * H d,
           fun d => Ay.add_mem (Ay.mul_mem (hGA d) hhA) (Ay.mul_mem hgA (hHA d)), fun k => ?_⟩
         rw [MvPolynomial.pderiv_mul, hG k, hH k, Finset.sum_mul, Finset.mul_sum,
           ← Finset.sum_add_distrib]
         refine Finset.sum_congr rfl fun d _ => ?_
         ring
       one_mem' := ⟨Ay.one_mem, fun _ => 0, fun _ => Ay.zero_mem, fun k => by simp⟩
       add_mem' := by
         rintro g h ⟨hgA, G, hGA, hG⟩ ⟨hhA, H, hHA, hH⟩
         refine ⟨Ay.add_mem hgA hhA, fun d => G d + H d, fun d => Ay.add_mem (hGA d) (hHA d),
           fun k => ?_⟩
         rw [map_add, hG k, hH k, ← Finset.sum_add_distrib]
         refine Finset.sum_congr rfl fun d _ => ?_
         ring
       zero_mem' := ⟨Ay.zero_mem, fun _ => 0, fun _ => Ay.zero_mem, fun k => by simp⟩
       algebraMap_mem' := fun r => ⟨Ay.algebraMap_mem r, fun _ => 0, fun _ => Ay.zero_mem,
         fun k => by simp [MvPolynomial.algebraMap_eq]⟩ }, fun g => Iff.rfl⟩

  have hxgen : ∀ a' b', ReciprocityTheory.ChartRestriction.G.TB.xForm (q := q) e a' b' ∈ Sx := by
    intro a' b'
    rw [hSx]
    refine ⟨fun j => ?_, fun d => if d = b' ∧ a' = a then 1 else 0, fun k => ?_⟩
    · simp [ReciprocityTheory.ChartRestriction.G.TB.xForm, map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        Pi.single_apply]
    · by_cases hab : a' = a
      · simp [ReciprocityTheory.ChartRestriction.G.TB.xForm, map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
          Pi.single_apply, hab]
      · simp [ReciprocityTheory.ChartRestriction.G.TB.xForm, map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
          Pi.single_apply, hab]
  have hygen : ∀ b' d', ReciprocityTheory.ChartRestriction.G.TB.yForm (p := p) f b' d' ∈ Sy := by
    intro b' d'
    rw [hSy, hAy]
    refine ⟨fun i => ?_, fun d => if d = d' ∧ b' = b then 1 else 0, fun d => ?_, fun k => ?_⟩
    · simp [ReciprocityTheory.ChartRestriction.G.TB.yForm, map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        Pi.single_apply]
    · dsimp only
      split_ifs
      · exact Ay.one_mem
      · exact Ay.zero_mem
    · by_cases hab : b' = b
      · simp [ReciprocityTheory.ChartRestriction.G.TB.yForm, map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
          Pi.single_apply, hab]
      · simp [ReciprocityTheory.ChartRestriction.G.TB.yForm, map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
          Pi.single_apply, hab]

  have hP : (∏ i, ReciprocityTheory.ChartRestriction.G.TB.leadMinor (Matrix.of (ReciprocityTheory.ChartRestriction.G.TB.xForm (q := q) e)) i ^ c i)
      ∈ Sx := by
    refine prod_mem fun i _ => pow_mem ?_ _
    refine det_mem_subalgebra_of_entries_mem Sx _ fun r s => ?_
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    exact hxgen _ _
  have hQ : (∏ i, ReciprocityTheory.ChartRestriction.G.TB.leadMinor (Matrix.of (ReciprocityTheory.ChartRestriction.G.TB.yForm (p := p) f)) i ^ c' i)
      ∈ Sy := by
    refine prod_mem fun i _ => pow_mem ?_ _
    refine det_mem_subalgebra_of_entries_mem Sy _ fun r s => ?_
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    exact hygen _ _
  have hdet : ReciprocityTheory.ChartRestriction.G.TB.detPoly e f c c' =
      (∏ i, ReciprocityTheory.ChartRestriction.G.TB.leadMinor (Matrix.of (ReciprocityTheory.ChartRestriction.G.TB.xForm (q := q) e)) i ^ c i) *
        ∏ i, ReciprocityTheory.ChartRestriction.G.TB.leadMinor (Matrix.of (ReciprocityTheory.ChartRestriction.G.TB.yForm (p := p) f)) i ^ c' i := rfl
  rw [hdet]
  generalize (∏ i, ReciprocityTheory.ChartRestriction.G.TB.leadMinor (Matrix.of (ReciprocityTheory.ChartRestriction.G.TB.xForm (q := q) e)) i ^ c i) = P at hP ⊢
  generalize (∏ i, ReciprocityTheory.ChartRestriction.G.TB.leadMinor (Matrix.of (ReciprocityTheory.ChartRestriction.G.TB.yForm (p := p) f)) i ^ c' i) = Q at hQ ⊢
  obtain ⟨hP0, G, hG⟩ := (hSx P).mp hP
  obtain ⟨-, H, hHA, hH⟩ := (hSy Q).mp hQ
  have hterm : ∀ k, MvPolynomial.pderiv (Sum.inl (a, k)) (MvPolynomial.pderiv (Sum.inr (b, k)) (P * Q)) =
      ∑ b', ∑ d, G b' * H d * MvPolynomial.C (e b' k * f d k) := by
    intro k
    have hHx : ∀ d, MvPolynomial.pderiv (Sum.inl (a, k)) (H d) = 0 := fun d => (hAy _).mp (hHA d) (a, k)
    rw [MvPolynomial.pderiv_mul, hP0 (b, k), zero_mul, zero_add, hH k, MvPolynomial.pderiv_mul, hG k]
    simp only [map_sum, MvPolynomial.pderiv_mul, hHx, MvPolynomial.pderiv_C, zero_mul, mul_zero,
      add_zero, Finset.sum_const_zero]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul]
    ring
  simp only [ReciprocityTheory.ChartRestriction.G.TB.mixedLap, LinearMap.sum_apply, LinearMap.comp_apply,
    Derivation.coeFn_coe]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_comm]
  refine Finset.sum_eq_zero fun b' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [← Finset.mul_sum, ← map_sum MvPolynomial.C, horth b' d, map_zero, mul_zero]
