-- Prove2me | solution 1 for cyclotomicCharacter_algebraicClosure_rat_surjective
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:24:16.97844+00:00
-- url     : https://prove2.me/submissions/fc5f2053-44ca-4f18-a6b7-19c6be32107c

import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

open Polynomial

theorem solution (p : ℕ) [Fact p.Prime] :
    Function.Surjective ((cyclotomicCharacter (AlgebraicClosure ℚ) p).comp
      (MulSemiringAction.toRingAut Gal(AlgebraicClosure ℚ/ℚ) (AlgebraicClosure ℚ))) := by
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.instIsAlgClosure ℚ
    · rfl
    · exact Subsingleton.elim _ _
  have : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  set Ω := AlgebraicClosure ℚ
  have : IsGalois ℚ Ω := IsGalois.mk
  set χ := (cyclotomicCharacter Ω p).comp (MulSemiringAction.toRingAut Gal(Ω/ℚ) Ω)
  have hcont : Continuous χ := cyclotomicCharacter.continuous p ℚ Ω
  have hclosed : IsClosed (Set.range χ) := (isCompact_range hcont).isClosed
  -- approximation at every finite level
  have happrox : ∀ (u : ℤ_[p]ˣ) (n : ℕ), ∃ σ : Gal(Ω/ℚ),
      PadicInt.toZModPow n (χ σ : ℤ_[p]) = PadicInt.toZModPow n (u : ℤ_[p]) := by
    intro u n
    have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ n)
    set a : ℕ := (PadicInt.toZModPow n (u : ℤ_[p])).val
    have hunit : IsUnit (PadicInt.toZModPow n (u : ℤ_[p])) := u.isUnit.map _
    have hcop : a.Coprime (p ^ n) := by
      have := ZMod.val_coe_unit_coprime hunit.unit
      simpa [a] using this
    have hζa : IsPrimitiveRoot (ζ ^ a) (p ^ n) := hζ.pow_of_coprime a hcop
    have hmin : minpoly ℚ (ζ ^ a) = minpoly ℚ ζ := by
      rw [← cyclotomic_eq_minpoly_rat hζa hpn, ← cyclotomic_eq_minpoly_rat hζ hpn]
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).1 hmin
    refine ⟨σ, ?_⟩
    have hspec := cyclotomicCharacter.spec (L := Ω) p
      (MulSemiringAction.toRingAut Gal(Ω/ℚ) Ω σ) ζ hζ.pow_eq_one
    have h1 : (MulSemiringAction.toRingAut Gal(Ω/ℚ) Ω σ) ζ = ζ ^ a := hσ
    rw [h1] at hspec
    have hord : orderOf ζ = p ^ n := hζ.eq_orderOf.symm
    have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨p ^ n, hpn, hζ.pow_eq_one⟩
    have hmod := hfin.pow_eq_pow_iff_modEq.1 hspec
    rw [hord] at hmod
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
    simp only [ZMod.natCast_val, ZMod.cast_id', id, a] at this
    exact this.symm
  intro u
  show u ∈ Set.range χ
  have hemb := (Units.isOpenEmbedding_val (R := ℤ_[p])).isEmbedding
  rw [← hclosed.closure_eq, hemb.closure_eq_preimage_closure_image, Set.mem_preimage,
    Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  obtain ⟨σ, hσ⟩ := happrox u n
  refine ⟨(χ σ : ℤ_[p]), ⟨χ σ, ⟨σ, rfl⟩, rfl⟩, lt_of_le_of_lt ?_ hn⟩
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, hσ, sub_self]
