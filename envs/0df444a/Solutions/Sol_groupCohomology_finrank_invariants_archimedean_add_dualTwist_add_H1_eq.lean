-- Prove2me | solution 1 for groupCohomology.finrank_invariants_archimedean_add_dualTwist_add_H1_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c0cae111-a31b-5b1e-aa9a-6f8fc2ece6b5

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Theorems.Thm_ExtCitation_cycloChar_complexConjugation_eq_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_invariants_archimedean_add_dualTwist_add_H1_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory Module groupCohomology P2MW.S_groupCohomology_finrank_invariants_archimedean_add_dualTwist_add_H1_eq.groupCohomology ExtCitation"

namespace ArchEigProof

open Classical

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

scoped instance : Finite Gc :=
  Finite.of_surjective (fun b : Bool => if b then (1 : Gc) else archimedeanGen) (by
    intro g; rcases eq_one_or_eq_gen g with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩)

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

theorem isLevelConstant₁_arch {X : Type*} (f : Gc → X) : IsLevelConstant₁ archimedeanLoc f := by
  obtain ⟨F, hF, hc⟩ := exists_level_not_fixed
  refine ⟨F, hF, fun g s hs => ?_⟩
  rcases eq_one_or_eq_gen s with rfl | rfl
  · rw [mul_one]
  · exact absurd hs hc

theorem isLevelConstant₂_arch {X : Type*} (f : Gc × Gc → X) : IsLevelConstant₂ archimedeanLoc f := by
  obtain ⟨F, hF, hc⟩ := exists_level_not_fixed
  refine ⟨F, hF, fun g g' s s' hs hs' => ?_⟩
  rcases eq_one_or_eq_gen s with rfl | rfl
  · rcases eq_one_or_eq_gen s' with rfl | rfl
    · rw [mul_one, mul_one]
    · exact absurd hs' hc
  · exact absurd hs hc

variable {p : ℕ} [Fact p.Prime] (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

noncomputable abbrev ρc : M →ₗ[ZMod p] M := M.ρ complexConjugation
noncomputable abbrev Nm : M →ₗ[ZMod p] M := ρc M - LinearMap.id
noncomputable abbrev Np : M →ₗ[ZMod p] M := ρc M + LinearMap.id

theorem ρc_ρc (m : M) : ρc M (ρc M m) = m := by
  change (M.ρ complexConjugation * M.ρ complexConjugation) m = m
  rw [← map_mul, complexConjugation_mul_self, map_one]; rfl

theorem Nm_Np (m : M) : Nm M (Np M m) = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, map_add, ρc_ρc]; abel

theorem Np_Nm (m : M) : Np M (Nm M m) = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, map_sub, ρc_ρc]; abel

theorem range_Np_le_ker_Nm : LinearMap.range (Np M) ≤ LinearMap.ker (Nm M) := by
  rintro _ ⟨m, rfl⟩; exact Nm_Np M m

theorem range_Nm_le_ker_Np : LinearMap.range (Nm M) ≤ LinearMap.ker (Np M) := by
  rintro _ ⟨m, rfl⟩; exact Np_Nm M m

theorem res_ρ_one (m : M) : (Rep.res archimedeanLoc M).ρ (1 : Gc) m = m := by rw [map_one]; rfl
theorem res_ρ_gen (m : M) : (Rep.res archimedeanLoc M).ρ (archimedeanGen : Gc) m = ρc M m := rfl

theorem invariants_eq_ker : ((Rep.res archimedeanLoc M).ρ.invariants : Submodule (ZMod p) M) = LinearMap.ker (Nm M) := by
  ext m
  rw [Representation.mem_invariants, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h; exact h archimedeanGen
  · intro h g
    rcases eq_one_or_eq_gen g with rfl | rfl
    · exact res_ρ_one M m
    · exact h

noncomputable def ev₁ : (Gc → M) →ₗ[ZMod p] M where
  toFun f := f archimedeanGen
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev₁_apply (f : Gc → M) : ev₁ M f = f archimedeanGen := rfl

theorem cocycle₁_values (f : ↥(cocycles₁ (Rep.res archimedeanLoc M))) :
    (f : Gc → M) 1 = 0 ∧ Np M ((f : Gc → M) archimedeanGen) = 0 := by
  have h1 : (f : Gc → M) 1 = 0 := cocycles₁_map_one f
  refine ⟨h1, ?_⟩
  have hf := (mem_cocycles₁_iff (f : Gc → M)).1 f.2 archimedeanGen archimedeanGen
  rw [gen_mul_gen, h1, res_ρ_gen] at hf
  rw [LinearMap.add_apply, LinearMap.id_apply]
  exact hf.symm

theorem cochain₁_ext {f g : Gc → M} (hf : f 1 = 0) (hg : g 1 = 0) (h : f archimedeanGen = g archimedeanGen) : f = g := by
  funext x
  rcases eq_one_or_eq_gen x with rfl | rfl
  · rw [hf, hg]
  · exact h

theorem mem_cocycles₁_of (m : M) (hm : Np M m = 0) :
    (fun g : Gc => if g = 1 then (0 : M) else m) ∈ cocycles₁ (Rep.res archimedeanLoc M) := by
  rw [mem_cocycles₁_iff]
  have hρm : ρc M m = -m := by
    rw [LinearMap.add_apply, LinearMap.id_apply] at hm
    exact eq_neg_of_add_eq_zero_left hm
  intro g h
  rcases eq_one_or_eq_gen g with rfl | rfl <;> rcases eq_one_or_eq_gen h with rfl | rfl
  · rw [mul_one, if_pos rfl, map_zero, add_zero]
  · rw [one_mul, if_neg gen_ne_one, if_pos rfl, res_ρ_one, add_zero]
  · rw [mul_one, if_pos rfl, if_neg gen_ne_one, map_zero, zero_add]
  · rw [gen_mul_gen, if_pos rfl, if_neg gen_ne_one, res_ρ_gen, hρm, neg_add_cancel]

theorem finrank_cocycles₁ [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) ↥(cocycles₁ (Rep.res archimedeanLoc M)) = finrank (ZMod p) ↥(LinearMap.ker (Np M)) := by
  classical

  let e : ↥(cocycles₁ (Rep.res archimedeanLoc M)) →ₗ[ZMod p] M := (ev₁ M).comp (Submodule.subtype _)
  have hinj : Function.Injective e := by
    intro f g hfg
    apply Subtype.ext
    exact cochain₁_ext M (cocycle₁_values M f).1 (cocycle₁_values M g).1 hfg
  have hrange : LinearMap.range e = LinearMap.ker (Np M) := by
    ext m
    constructor
    · rintro ⟨f, rfl⟩; exact (cocycle₁_values M f).2
    · intro hm
      exact ⟨⟨_, mem_cocycles₁_of M m hm⟩, if_neg gen_ne_one⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]

theorem coboundaries₁_eq : (coboundaries₁ (Rep.res archimedeanLoc M) : Submodule (ZMod p) (Gc → M))
    = (LinearMap.range (Nm M)).comap (ev₁ M) ⊓ cocycles₁ (Rep.res archimedeanLoc M) := by
  ext f
  constructor
  · intro hf
    refine ⟨?_, coboundaries₁_le_cocycles₁ _ hf⟩
    obtain ⟨m, rfl⟩ := hf
    refine ⟨m, ?_⟩
    change Nm M m = (d₀₁ (Rep.res archimedeanLoc M)).hom m archimedeanGen
    rw [d₀₁_hom_apply, res_ρ_gen, LinearMap.sub_apply, LinearMap.id_apply]
  · rintro ⟨⟨m, hm⟩, hf⟩
    refine ⟨m, ?_⟩
    have h0 : (d₀₁ (Rep.res archimedeanLoc M)).hom m 1 = 0 := by rw [d₀₁_hom_apply, res_ρ_one, sub_self]
    refine cochain₁_ext M h0 (cocycles₁_map_one ⟨f, hf⟩) ?_
    rw [d₀₁_hom_apply, res_ρ_gen]
    rw [ev₁_apply] at hm
    rw [← hm, LinearMap.sub_apply, LinearMap.id_apply]

theorem finrank_coboundaries₁ [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) ↥(coboundaries₁ (Rep.res archimedeanLoc M)) = finrank (ZMod p) ↥(LinearMap.range (Nm M)) := by
  classical
  let e : ↥(coboundaries₁ (Rep.res archimedeanLoc M)) →ₗ[ZMod p] M := (ev₁ M).comp (Submodule.subtype _)
  have hinj : Function.Injective e := by
    intro f g hfg
    apply Subtype.ext
    exact cochain₁_ext M (cocycles₁_map_one ⟨f.1, coboundaries₁_le_cocycles₁ _ f.2⟩)
      (cocycles₁_map_one ⟨g.1, coboundaries₁_le_cocycles₁ _ g.2⟩) hfg
  have hrange : LinearMap.range e = LinearMap.range (Nm M) := by
    ext m
    constructor
    · rintro ⟨⟨f, hf⟩, rfl⟩
      rw [coboundaries₁_eq] at hf
      exact hf.1
    · rintro ⟨x, rfl⟩
      refine ⟨⟨(d₀₁ (Rep.res archimedeanLoc M)).hom x, ⟨x, rfl⟩⟩, ?_⟩
      change (d₀₁ (Rep.res archimedeanLoc M)).hom x archimedeanGen = Nm M x
      rw [d₀₁_hom_apply, res_ρ_gen, LinearMap.sub_apply, LinearMap.id_apply]
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]

theorem finrank_H1 [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) (H1 (Rep.res archimedeanLoc M)) + finrank (ZMod p) ↥(LinearMap.range (Nm M))
      = finrank (ZMod p) ↥(LinearMap.ker (Np M)) := by
  let π : ↥(cocycles₁ (Rep.res archimedeanLoc M)) →ₗ[ZMod p] H1 (Rep.res archimedeanLoc M) := (H1π (Rep.res archimedeanLoc M)).hom
  have hsurj : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    induction x using H1_induction_on with
    | _ f => exact ⟨f, rfl⟩
  have hker : LinearMap.ker π = (coboundaries₁ (Rep.res archimedeanLoc M)).comap (cocycles₁ (Rep.res archimedeanLoc M)).subtype := by
    ext f
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    exact H1π_eq_zero_iff f
  have hrn := LinearMap.finrank_range_add_finrank_ker π
  rw [hsurj, finrank_top, hker, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (coboundaries₁_le_cocycles₁ _)),
    finrank_coboundaries₁, finrank_cocycles₁] at hrn
  exact hrn

noncomputable def ev₂ : (Gc × Gc → M) →ₗ[ZMod p] M where
  toFun f := f (archimedeanGen, archimedeanGen) + f (1, 1)
  map_add' f g := by simp only [Pi.add_apply]; abel
  map_smul' a f := by simp only [Pi.smul_apply, smul_add, RingHom.id_apply]

theorem ev₂_apply (f : Gc × Gc → M) : ev₂ M f = f (archimedeanGen, archimedeanGen) + f (1, 1) := rfl

theorem d₁₂_apply (u : Gc → M) (g h : Gc) :
    (d₁₂ (Rep.res archimedeanLoc M)).hom u (g, h) = (Rep.res archimedeanLoc M).ρ g (u h) - u (g * h) + u g := by
  rw [d₁₂_hom_apply]

theorem cocycle₂_values (f : Gc × Gc → M) (hf : f ∈ cocycles₂ (Rep.res archimedeanLoc M)) :
    f (1, archimedeanGen) = f (1, 1) ∧ f (archimedeanGen, 1) = ρc M (f (1, 1)) ∧ Nm M (ev₂ M f) = 0 := by
  rw [mem_cocycles₂_iff] at hf
  have hb : f (1, archimedeanGen) = f (1, 1) := by
    have h := hf 1 1 archimedeanGen
    rw [one_mul, one_mul, res_ρ_one] at h
    exact (add_left_cancel h).symm
  have hd : f (archimedeanGen, 1) = ρc M (f (1, 1)) := by
    have h := hf archimedeanGen 1 1
    rw [mul_one, mul_one, res_ρ_gen] at h
    exact add_right_cancel h
  refine ⟨hb, hd, ?_⟩
  have h := hf archimedeanGen archimedeanGen archimedeanGen
  rw [gen_mul_gen, hb, hd, res_ρ_gen] at h

  rw [ev₂_apply, LinearMap.sub_apply, LinearMap.id_apply, map_add, sub_eq_zero]
  calc ρc M (f (archimedeanGen, archimedeanGen)) + ρc M (f (1, 1)) = f (1, 1) + f (archimedeanGen, archimedeanGen) := h.symm
    _ = _ := add_comm _ _

theorem mem_levelCocycles₂_of (m : M) (hm : Nm M m = 0) :
    (fun gh : Gc × Gc => if gh.1 = 1 then (0 : M) else if gh.2 = 1 then 0 else m)
      ∈ levelCocycles₂ archimedeanLoc (Rep.res archimedeanLoc M) := by
  have hρm : ρc M m = m := by
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hm; exact hm
  refine (mem_levelCocycles₂_iff _ _ _).2 ⟨?_, isLevelConstant₂_arch _⟩
  rw [mem_cocycles₂_iff]
  intro g h j
  rcases eq_one_or_eq_gen g with rfl | rfl <;> rcases eq_one_or_eq_gen h with rfl | rfl <;>
    rcases eq_one_or_eq_gen j with rfl | rfl
  all_goals simp [res_ρ_one, res_ρ_gen, gen_ne_one, gen_mul_gen, hρm]

theorem mem_levelCoboundaries₂_of (f : Gc × Gc → M) (hf : f ∈ cocycles₂ (Rep.res archimedeanLoc M))
    (y : M) (hy : ev₂ M f = Np M y) : f ∈ levelCoboundaries₂ archimedeanLoc (Rep.res archimedeanLoc M) := by
  classical
  obtain ⟨hb, hd, -⟩ := cocycle₂_values M f hf
  rw [mem_levelCoboundaries₂_iff]
  let a : M := f (1, 1)
  let u : Gc → M := fun g => if g = 1 then a else y
  refine ⟨u, isLevelConstant₁_arch u, ?_⟩
  have hu1 : u 1 = a := if_pos rfl
  have huc : u archimedeanGen = y := if_neg gen_ne_one
  have he : f (archimedeanGen, archimedeanGen) = Np M y - a := by
    rw [← hy, ev₂_apply]; abel
  funext ⟨g, h⟩
  rw [d₁₂_apply]
  rcases eq_one_or_eq_gen g with rfl | rfl <;> rcases eq_one_or_eq_gen h with rfl | rfl
  · rw [res_ρ_one, mul_one, hu1]; change a - a + a = a; abel
  · rw [res_ρ_one, one_mul, huc, hu1, hb]; change y - y + a = a; abel
  · rw [mul_one, res_ρ_gen, hu1, huc, hd]; change ρc M a - y + y = ρc M a; abel
  · rw [gen_mul_gen, res_ρ_gen, huc, hu1, he, LinearMap.add_apply, LinearMap.id_apply]; abel

theorem finrank_continuousH2 [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) (continuousH2 archimedeanLoc (Rep.res archimedeanLoc M)) + finrank (ZMod p) ↥(LinearMap.range (Np M))
      = finrank (ZMod p) ↥(LinearMap.ker (Nm M)) := by
  classical
  dsimp only [continuousH2]
  set Z := levelCocycles₂ archimedeanLoc (Rep.res archimedeanLoc M) with hZ
  set B := (levelCoboundaries₂ archimedeanLoc (Rep.res archimedeanLoc M)).comap Z.subtype with hB

  let T : ↥Z →ₗ[ZMod p] M := (ev₂ M).comp Z.subtype
  have hTrange : LinearMap.range T = LinearMap.ker (Nm M) := by
    ext m; constructor
    · rintro ⟨f, rfl⟩; exact (cocycle₂_values M (f : Gc × Gc → M) f.2.1).2.2
    · intro hm
      refine ⟨⟨_, mem_levelCocycles₂_of M m hm⟩, ?_⟩
      change ev₂ M (fun gh : Gc × Gc => if gh.1 = 1 then (0 : M) else if gh.2 = 1 then 0 else m) = m
      rw [ev₂_apply]; simp [gen_ne_one]
  have hB' : B = (LinearMap.range (Np M)).comap T := by
    ext f
    rw [hB, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_comap]
    constructor
    · intro hf
      obtain ⟨u, -, hu⟩ := (mem_levelCoboundaries₂_iff _ _ _).1 hf
      refine ⟨u archimedeanGen, ?_⟩
      change Np M (u archimedeanGen) = ev₂ M (f : Gc × Gc → M)
      rw [← hu, ev₂_apply, d₁₂_apply, d₁₂_apply, gen_mul_gen, mul_one, res_ρ_gen, res_ρ_one,
        LinearMap.add_apply, LinearMap.id_apply]
      abel
    · rintro ⟨y, hy⟩
      exact mem_levelCoboundaries₂_of M (f : Gc × Gc → M) f.2.1 y hy.symm

  have h1 := Submodule.finrank_quotient_add_finrank B
  have h2 := LinearMap.finrank_range_add_finrank_ker T
  rw [hTrange] at h2

  let TB : ↥B →ₗ[ZMod p] M := T.comp B.subtype
  have hTBrange : LinearMap.range TB = LinearMap.range (Np M) := by
    ext m; constructor
    · rintro ⟨⟨f, hf⟩, rfl⟩
      rw [hB'] at hf; exact hf
    · intro hm
      have hm' : m ∈ LinearMap.range T := by rw [hTrange]; exact range_Np_le_ker_Nm M hm
      obtain ⟨f, rfl⟩ := hm'
      exact ⟨⟨f, by rw [hB']; exact hm⟩, rfl⟩
  have hle : LinearMap.ker T ≤ B := by
    intro f hf
    rw [hB', Submodule.mem_comap, LinearMap.mem_ker.1 hf]
    exact zero_mem _
  have hkerTB : LinearMap.ker TB = (LinearMap.ker T).comap B.subtype := by
    ext f; rfl
  have h3 := LinearMap.finrank_range_add_finrank_ker TB
  rw [hTBrange, hkerTB, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at h3

  rw [← h3, ← add_assoc, ← h2] at h1
  exact Nat.add_right_cancel h1

theorem invariants_dualTwist_eq [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) ↥((Rep.res archimedeanLoc (M.dualTwist (cycloChar p))).ρ.invariants) + finrank (ZMod p) ↥(LinearMap.range (Np M))
      = finrank (ZMod p) M := by
  have hχ : ((cycloChar p complexConjugation : (ZMod p)ˣ) : ZMod p) = -1 := by
    rw [cycloChar_complexConjugation_eq_neg_one, Units.val_neg, Units.val_one]
  have heq : ((Rep.res archimedeanLoc (M.dualTwist (cycloChar p))).ρ.invariants : Submodule (ZMod p) (Module.Dual (ZMod p) M))
      = (LinearMap.range (Np M)).dualAnnihilator := by
    ext φ
    rw [Representation.mem_invariants, Submodule.mem_dualAnnihilator]
    have key : ∀ φ : Module.Dual (ZMod p) M,
        (Rep.res archimedeanLoc (M.dualTwist (cycloChar p))).ρ archimedeanGen φ = -(φ ∘ₗ ρc M) := by
      intro φ
      change (M.dualTwist (cycloChar p)).ρ complexConjugation φ = _
      rw [Rep.dualTwist_ρ_apply, complexConjugation_inv, hχ]
      ext m
      simp
    constructor
    · intro h w hw
      obtain ⟨m, rfl⟩ := hw
      have hc := h archimedeanGen
      rw [key] at hc
      have := congrArg (fun ψ : Module.Dual (ZMod p) M => ψ m) hc
      simp only [LinearMap.neg_apply, LinearMap.comp_apply] at this
      rw [LinearMap.add_apply, LinearMap.id_apply, map_add]

      rw [← this]; abel
    · intro h g
      rcases eq_one_or_eq_gen g with rfl | rfl
      · rw [map_one]; rfl
      · rw [key]
        apply LinearMap.ext; intro m
        simp only [LinearMap.neg_apply, LinearMap.comp_apply]
        have := h (Np M m) ⟨m, rfl⟩
        rw [LinearMap.add_apply, LinearMap.id_apply, map_add] at this

        exact neg_eq_of_add_eq_zero_right this
  rw [heq, add_comm]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq _

end ArchEigProof
p2m_reactivate "P2MW.S_groupCohomology_finrank_invariants_archimedean_add_dualTwist_add_H1_eq.ArchEigProof"

namespace groupCohomology p2m_export "groupCohomology" "d₁₂ coboundaries₁ H1π mem_cocycles₁_iff H1_induction_on cocycles₂ H1π_eq_zero_iff cocycles₁_map_one d₁₂_hom_apply coboundaries₁_le_cocycles₁ cocycles mem_cocycles₂_iff π d₀₁_hom_apply cocycles₁ d₀₁ H1 IsLevelConstant₁ IsLevelConstant₂ levelCocycles₂ mem_levelCocycles₂_iff levelCoboundaries₂ mem_levelCoboundaries₂_iff continuousH2" end groupCohomology
p2m_open_scoped "groupCohomology" in
open ArchEigProof in
theorem groupCohomology.finrank_invariants_archimedean_add_dualTwist_add_H1_eq_core
    {p : ℕ} [Fact p.Prime]
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) (Rep.res archimedeanLoc M).ρ.invariants
      + finrank (ZMod p) (Rep.res archimedeanLoc (M.dualTwist (cycloChar p))).ρ.invariants
      + finrank (ZMod p) (H1 (Rep.res archimedeanLoc M))
    = finrank (ZMod p) M
      + 2 * finrank (ZMod p) (continuousH2 archimedeanLoc (Rep.res archimedeanLoc M)) := by
  have hA : finrank (ZMod p) ↥(Rep.res archimedeanLoc M).ρ.invariants = finrank (ZMod p) ↥(LinearMap.ker (Nm M)) := by
    rw [invariants_eq_ker]
  have hB := finrank_H1 M
  have hC := finrank_continuousH2 M
  have hD := invariants_dualTwist_eq M
  have hm := LinearMap.finrank_range_add_finrank_ker (Nm M)
  have hp := LinearMap.finrank_range_add_finrank_ker (Np M)
  omega

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) M).ρ.invariants
      + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist (cycloChar p))).ρ.invariants
      + finrank (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))
    = finrank (ZMod p) M
      + 2 * finrank (ZMod p)
          (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)) :=
  groupCohomology.finrank_invariants_archimedean_add_dualTwist_add_H1_eq_core M

end S_groupCohomology_finrank_invariants_archimedean_add_dualTwist_add_H1_eq
end P2MW
export P2MW.S_groupCohomology_finrank_invariants_archimedean_add_dualTwist_add_H1_eq (solution)
