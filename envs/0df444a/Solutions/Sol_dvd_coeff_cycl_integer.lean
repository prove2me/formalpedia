-- Prove2me | solution 1 for dvd_coeff_cycl_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:36.41111+00:00
-- url     : https://prove2.me/submissions/2f88bc65-6964-4178-ba9c-9041b990fb32

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat

set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional Polynomial Algebra Nat Finset Fintype
variable (p : ℕ) (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
open scoped NumberField
open Ideal IsCyclotomicExtension
local notation "R" => 𝓞 (CyclotomicField p ℚ)
variable {p}
open IsPrimitiveRoot
variable {L}
theorem _root_.solution (hp : p.Prime) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p)
    {f : Fin p → ℤ} (hf : ∃ i, f i = 0) {m : ℤ}
    (hdiv : ↑m ∣ ∑ j, f j • ζ ^ (j : ℕ)) : ∀ j, m ∣ f j := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p.pred, (succ_pred_prime hp).symm⟩
  have hζ' : IsPrimitiveRoot (ζ : L) (n + 1) := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  set b := hζ'.integralPowerBasis with hb
  have hdim : b.dim = n := by rw [hb, hζ'.integralPowerBasis_dim, totient_prime hp,
    Nat.add_sub_cancel]
  have hbasis (i : Fin b.dim) : b.basis i = ζ ^ (i : ℕ) := by
    rw [PowerBasis.basis_eq_pow, show b.gen = hζ'.toInteger from hζ'.integralPowerBasis_gen]
    rfl
  have hgeom : ∑ i : Fin n, ζ ^ (i : ℕ) = -ζ ^ n := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ ζ ^ i) n]
    exact eq_neg_of_add_eq_zero_left
      (by simpa [sum_range_succ] using hζ.geom_sum_eq_zero hp.one_lt)
  -- Since `ζ ^ n = -(1 + ζ + ⋯ + ζ ^ (n - 1))`, the sum `∑ j, f j • ζ ^ j` has
  -- coordinates `f j - f (Fin.last n)` in the integral power basis `1, ζ, …, ζ ^ (n - 1)`.
  have hsum : (∑ j, f j • ζ ^ (j : ℕ)) = b.basis.equivFun.symm
      fun i ↦ f ⟨i, (i.2.trans_le hdim.le).trans n.lt_succ_self⟩ - f (Fin.last n) := by
    rw [Module.Basis.equivFun_symm_apply, Fintype.sum_equiv (finCongr hdim)
      (fun i : Fin b.dim ↦
        (f ⟨i, (i.2.trans_le hdim.le).trans n.lt_succ_self⟩ - f (Fin.last n)) • b.basis i)
      (fun i : Fin n ↦ (f ⟨i, i.2.trans n.lt_succ_self⟩ - f (Fin.last n)) • ζ ^ (i : ℕ))
      fun i ↦ by
        rw [hbasis]
        rfl]
    simp only [sub_smul, sum_sub_distrib, ← Finset.smul_sum, hgeom, smul_neg, sub_neg_eq_add]
    exact Fin.sum_univ_castSucc fun j : Fin (n + 1) ↦ f j • ζ ^ (j : ℕ)
  obtain ⟨y, hy⟩ := hdiv
  rw [hsum, ← zsmul_eq_mul] at hy
  have key (i : Fin b.dim) :
      m ∣ f ⟨i, (i.2.trans_le hdim.le).trans n.lt_succ_self⟩ - f (Fin.last n) := by
    have h1 : f ⟨i, (i.2.trans_le hdim.le).trans n.lt_succ_self⟩ - f (Fin.last n) =
        b.basis.coord i (m • y) := by rw [← hy, b.basis.coord_equivFun_symm]
    rw [h1]
    exact b.basis.dvd_coord_smul i y m
  have hlast : m ∣ f (Fin.last n) := by
    obtain ⟨i, hi⟩ := hf
    rcases (Nat.lt_succ_iff.mp i.2).eq_or_lt with h | h
    · rw [← show i = Fin.last n from Fin.ext h, hi]
      exact dvd_zero m
    · simpa [hi] using key ⟨i, hdim.symm ▸ h⟩
  intro j
  rcases (Nat.lt_succ_iff.mp j.2).eq_or_lt with h | h
  · exact (show j = Fin.last n from Fin.ext h) ▸ hlast
  · simpa using (key ⟨j, hdim.symm ▸ h⟩).add hlast
