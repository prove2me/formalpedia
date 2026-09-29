-- Prove2me | solution 1 for groupCohomology.exists_injective_dual_continuousH2_archimedean
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e347b2ec-340e-50b2-ae57-7218540cbb35

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_injective_dual_continuousH2_archimedean

set_option autoImplicit false

p2m_open "CategoryTheory Module groupCohomology P2MW.S_groupCohomology_exists_injective_dual_continuousH2_archimedean.groupCohomology ExtCitation"

namespace ArchInvProof

abbrev Gc : Type := ↥archimedeanDecomposition

theorem gen_mul_gen : (archimedeanGen * archimedeanGen : Gc) = 1 := Subtype.ext complexConjugation_mul_self

theorem eq_one_or_eq_gen (g : Gc) : g = 1 ∨ g = archimedeanGen := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  have h2 : (complexConjugation : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, complexConjugation_mul_self]
  have hkey : (complexConjugation : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ^ n = complexConjugation ^ (n % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod n 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    apply Subtype.ext
    change (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1
    rw [← hn, hkey, h0, zpow_zero]
  · right
    apply Subtype.ext
    change (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = complexConjugation
    rw [← hn, hkey, h1, zpow_one]

theorem exists_level_not_fixed :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ complexConjugation ∉ F.fixingSubgroup := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : AlgebraicClosure ℚ)
  have hint : IsIntegral ℚ i := by
    refine ⟨Polynomial.X ^ 2 + 1, Polynomial.monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [pow_two, ← hi]
  refine ⟨IntermediateField.adjoin ℚ {i}, IntermediateField.adjoin.finiteDimensional hint, fun hc => ?_⟩
  have hfix : complexConjugation i = i :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hc i (IntermediateField.mem_adjoin_simple_self ℚ i)
  have hz := complexEmbedding_complexConjugation i
  rw [hfix] at hz
  set z := complexEmbedding i with hzdef
  have hz2 : z * z = -1 := by rw [hzdef, ← map_mul, ← hi, map_neg, map_one]
  have him : z.im = 0 := by
    have := congrArg Complex.im hz.symm
    simp only [Complex.conj_im] at this
    linarith
  have hre : (z * z).re = z.re * z.re := by simp [Complex.mul_re, him]
  rw [hz2] at hre
  simp only [Complex.neg_re, Complex.one_re] at hre
  nlinarith [mul_self_nonneg z.re]

theorem gen_ne_one : (archimedeanGen : Gc) ≠ 1 := by
  intro h
  obtain ⟨F, -, hF⟩ := exists_level_not_fixed
  apply hF
  have : complexConjugation = ((1 : Gc) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := congrArg Subtype.val h
  rw [this]
  exact one_mem _

theorem eq_one_of_loc_mem {F : IntermediateField ℚ (AlgebraicClosure ℚ)} (hF : complexConjugation ∉ F.fixingSubgroup)
    {s : Gc} (hs : archimedeanLoc s ∈ F.fixingSubgroup) : s = 1 := by
  rcases eq_one_or_eq_gen s with rfl | rfl
  · rfl
  · exact absurd hs hF

theorem isLevelConstant₁_arch {X : Type*} (f : Gc → X) : IsLevelConstant₁ archimedeanLoc f := by
  obtain ⟨F, hF, hc⟩ := exists_level_not_fixed
  exact ⟨F, hF, fun g s hs => by rw [eq_one_of_loc_mem hc hs, mul_one]⟩

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev Mc : Rep (ZMod p) Gc := ofChar (k := ZMod p) ((cycloChar p).comp archimedeanLoc)

noncomputable def eps : ZMod p := (((cycloChar p).comp archimedeanLoc (archimedeanGen : Gc) : (ZMod p)ˣ) : ZMod p)

theorem rho_one (x : Mc p) : (Mc p).ρ 1 x = x := by rw [map_one]; rfl

theorem rho_gen (x : Mc p) : (Mc p).ρ archimedeanGen x = eps p * x := by
  simp [Representation.twist_apply_apply, eps]

theorem eps_mul_eps : eps p * eps p = 1 := by
  rw [eps, ← Units.val_mul, ← map_mul, gen_mul_gen, map_one, Units.val_one]

theorem cocycle_values (f : Gc × Gc → Mc p) (hf : f ∈ cocycles₂ (Mc p)) :
    f (1, archimedeanGen) = f (1, 1) ∧ f (archimedeanGen, 1) = eps p * f (1, 1) := by
  rw [mem_cocycles₂_iff] at hf
  constructor
  · have h := hf 1 1 archimedeanGen
    rw [one_mul, one_mul, rho_one] at h
    exact (add_left_cancel h).symm
  · have h := hf archimedeanGen 1 1
    rw [mul_one, mul_one, rho_gen] at h
    exact add_right_cancel h

theorem d_apply (u : Gc → Mc p) (g h : Gc) : (d₁₂ (Mc p)).hom u (g, h) = (Mc p).ρ g (u h) - u (g * h) + u g :=
  d₁₂_hom_apply (Mc p) u (g, h)

end ArchInvProof

namespace groupCohomology p2m_export "groupCohomology" "d₁₂ cocycles₂ d₁₂_hom_apply mem_cocycles₂_iff ofChar IsLevelConstant₁ isLevelConstant₁_const levelCocycles₂ levelCoboundaries₂ mem_levelCoboundaries₂_iff continuousH2" end groupCohomology
p2m_open_scoped "groupCohomology" in
open ArchInvProof in
theorem groupCohomology.exists_injective_dual_continuousH2_archimedean_core (p : ℕ) [Fact p.Prime] :
    ∃ inv : continuousH2 archimedeanLoc (Mc p) →ₗ[ZMod p] ZMod p, Function.Injective inv := by
  classical
  by_cases hε : eps p = -1
  ·
    let ev : (Gc × Gc → Mc p) → ZMod p := fun f => f (archimedeanGen, archimedeanGen) + f (1, 1)
    let L : ↥(levelCocycles₂ archimedeanLoc (Mc p)) →ₗ[ZMod p] ZMod p :=
      { toFun := fun f => ev (f : Gc × Gc → Mc p)
        map_add' := fun f g => by
          simp only [ev, Submodule.coe_add, Pi.add_apply]; ring
        map_smul' := fun a f => by
          simp only [ev, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have hL : ∀ f : ↥(levelCocycles₂ archimedeanLoc (Mc p)),
        L f = (f : Gc × Gc → Mc p) (archimedeanGen, archimedeanGen) + (f : Gc × Gc → Mc p) (1, 1) := fun f => rfl
    have hLker : ∀ f : ↥(levelCocycles₂ archimedeanLoc (Mc p)),
        (f : Gc × Gc → Mc p) ∈ levelCoboundaries₂ archimedeanLoc (Mc p) → L f = 0 := by
      intro f hf
      obtain ⟨u, -, hu⟩ := (mem_levelCoboundaries₂_iff archimedeanLoc (Mc p) _).1 hf
      rw [hL, ← hu, d_apply, d_apply, gen_mul_gen, mul_one, rho_gen, rho_one, hε]
      ring
    refine ⟨Submodule.liftQ _ L (fun f hf => (LinearMap.mem_ker).2 (hLker f hf)), ?_⟩
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ (fun f hf => ?_)
    rw [LinearMap.mem_ker, hL] at hf
    rw [Submodule.mem_comap, Submodule.subtype_apply, mem_levelCoboundaries₂_iff]
    obtain ⟨hb, hdv⟩ := cocycle_values p (f : Gc × Gc → Mc p) f.2.1
    refine ⟨fun _ => (f : Gc × Gc → Mc p) (1, 1), isLevelConstant₁_const archimedeanLoc _, ?_⟩
    have hcc : (f : Gc × Gc → Mc p) (archimedeanGen, archimedeanGen) = - (f : Gc × Gc → Mc p) (1, 1) :=
      eq_neg_of_add_eq_zero_left hf
    funext ⟨g, h⟩
    rw [d_apply]
    rcases eq_one_or_eq_gen g with rfl | rfl <;> rcases eq_one_or_eq_gen h with rfl | rfl
    · rw [rho_one]; abel
    · rw [rho_one, hb]; abel
    · rw [rho_gen, hdv]; abel
    · rw [rho_gen, hcc, hε]; ring
  ·
    have hε1 : eps p = 1 := by
      rcases mul_self_eq_one_iff.1 (eps_mul_eps p) with h | h
      · exact h
      · exact absurd h hε
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h2
      apply hε
      rw [hε1]
      have : (1 : ZMod p) + 1 = 0 := by rw [← two_mul, mul_one]; exact h2
      exact eq_neg_of_add_eq_zero_left this
    refine ⟨0, fun x y _ => ?_⟩
    suffices hzero : ∀ z : continuousH2 archimedeanLoc (Mc p), z = 0 by rw [hzero x, hzero y]
    intro z
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ z
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      mem_levelCoboundaries₂_iff]
    obtain ⟨hb, hdv⟩ := cocycle_values p (f : Gc × Gc → Mc p) f.2.1
    let a : Mc p := (f : Gc × Gc → Mc p) (1, 1)
    let e : Mc p := (f : Gc × Gc → Mc p) (archimedeanGen, archimedeanGen)
    let u : Gc → Mc p := fun g => if g = 1 then a else (2 : ZMod p)⁻¹ * (e + a)
    have hu1 : u 1 = a := if_pos rfl
    have huc : u archimedeanGen = (2 : ZMod p)⁻¹ * (e + a) := if_neg gen_ne_one
    refine ⟨u, isLevelConstant₁_arch u, ?_⟩
    funext ⟨g, h⟩
    rw [d_apply]
    rcases eq_one_or_eq_gen g with rfl | rfl <;> rcases eq_one_or_eq_gen h with rfl | rfl
    · rw [rho_one, mul_one, hu1]
      change a - a + a = a
      abel
    · rw [rho_one, one_mul, huc, hu1, hb]
      change _ = a
      abel
    · rw [mul_one, rho_gen, hu1, huc, hdv, hε1]
      change (1 : ZMod p) * a - _ + _ = 1 * a
      ring
    · rw [gen_mul_gen, rho_gen, huc, hu1, hε1]
      change (1 : ZMod p) * ((2 : ZMod p)⁻¹ * (e + a)) - a + (2 : ZMod p)⁻¹ * (e + a) = e
      field_simp
      ring

theorem solution
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) :
    ∃ inv : continuousH2 (extArithLoc S (Sum.inl ()))
        (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inl ())))) →ₗ[ZMod p] ZMod p,
      Function.Injective inv :=
  groupCohomology.exists_injective_dual_continuousH2_archimedean_core p

end S_groupCohomology_exists_injective_dual_continuousH2_archimedean
end P2MW
export P2MW.S_groupCohomology_exists_injective_dual_continuousH2_archimedean (solution)
