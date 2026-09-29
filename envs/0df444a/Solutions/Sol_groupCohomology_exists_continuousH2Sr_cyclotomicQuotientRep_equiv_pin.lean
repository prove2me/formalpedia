-- Prove2me | solution 1 for groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/86734805-999b-5489-9382-cca30eee0c2b

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_Rep_QuotientRightTranslation
import Definitions.Def_GroupCohomology_CyclotomicQuotientH2Rep
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Theorems.Thm_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"

local instance RelSh2.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance RelSh2.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance RelSh2.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace RelSh2

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma conj_mem_fixingSubgroup (E : IntermediateField ℚ Qbar) [Normal ℚ E] {s : Γ} (hs : s ∈ E.fixingSubgroup) (x : Γ) :
    x * s * x⁻¹ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro y hy
  have hle := IntermediateField.normal_iff_forall_map_le'.mp (inferInstance : Normal ℚ E) x⁻¹
  have hy' : x⁻¹ y ∈ E := hle ⟨y, hy, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hy']
  simp

lemma exists_normal_level {S : Finset Nat.Primes} {F : IntermediateField ℚ Qbar} (hF : F.IsUnramifiedOutside S) :
    ∃ N : IntermediateField ℚ Qbar, N.IsUnramifiedOutside S ∧ N.fixingSubgroup ≤ F.fixingSubgroup ∧
      ∀ (s : Γ), s ∈ N.fixingSubgroup → ∀ x : Γ, x⁻¹ * s * x ∈ N.fixingSubgroup := by
  haveI : FiniteDimensional ℚ ↥F := hF.1
  refine ⟨IntermediateField.normalClosure ℚ (↥F) Qbar, IntermediateField.IsUnramifiedOutside.normalClosure hF,
    IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F), fun s hs x => ?_⟩
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ (↥F) Qbar) := normalClosure.normal ℚ (↥F) Qbar
  have := conj_mem_fixingSubgroup (IntermediateField.normalClosure ℚ (↥F) Qbar) hs x⁻¹
  rwa [inv_inv] at this

section TwistedConj
variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* Γ) (S : Finset Nat.Primes)
  {A : Rep.{0} k G} (f : G →* G) (γ : Γ) (hf : ∀ g : G, r (f g) = γ⁻¹ * r g * γ)
  (φ : A →ₗ[k] A) (hφ : ∀ (g : G) (a : A), φ (A.ρ (f g) a) = A.ρ g (φ a))

include hf in
lemma isLevelConstantSr₁_pullPush {x : G → A} (hx : IsLevelConstantSr₁ r S x) : IsLevelConstantSr₁ r S (cochainsPullPush₁ f φ x) := by
  obtain ⟨F, hF, h⟩ := hx
  obtain ⟨N, hN, hNF, hconj⟩ := exists_normal_level hF
  refine ⟨N, hN, fun g s hs => ?_⟩
  simp only [cochainsPullPush₁_apply, map_mul]
  congr 1
  apply h
  rw [hf]
  exact hNF (hconj _ hs γ)

include hf in
lemma isLevelConstantSr₂_pullPush {x : G × G → A} (hx : IsLevelConstantSr₂ r S x) : IsLevelConstantSr₂ r S (cochainsPullPush₂ f φ x) := by
  obtain ⟨F, hF, h⟩ := hx
  obtain ⟨N, hN, hNF, hconj⟩ := exists_normal_level hF
  refine ⟨N, hN, fun g g' s s' hs hs' => ?_⟩
  simp only [cochainsPullPush₂_apply, map_mul]
  congr 1
  apply h
  · rw [hf]; exact hNF (hconj _ hs γ)
  · rw [hf]; exact hNF (hconj _ hs' γ)

include hf hφ in
lemma pullPush_mem_levelCocyclesSr₂ {x : G × G → A} (hx : x ∈ levelCocyclesSr₂ r S A) :
    cochainsPullPush₂ f φ x ∈ levelCocyclesSr₂ r S A := by
  rw [mem_levelCocyclesSr₂_iff] at hx ⊢
  exact ⟨cochainsPullPush₂_mem_cocycles₂ f φ hφ hx.1, isLevelConstantSr₂_pullPush r S f γ hf φ hx.2⟩

include hf hφ in
lemma pullPush_mem_levelCoboundariesSr₂ {x : G × G → A} (hx : x ∈ levelCoboundariesSr₂ r S A) :
    cochainsPullPush₂ f φ x ∈ levelCoboundariesSr₂ r S A := by
  obtain ⟨y, hy, rfl⟩ := (mem_levelCoboundariesSr₂_iff r S A x).1 hx
  exact (mem_levelCoboundariesSr₂_iff r S A _).2
    ⟨cochainsPullPush₁ f φ y, isLevelConstantSr₁_pullPush r S f γ hf φ hy, (cochainsPullPush₂_d₁₂ f φ hφ y).symm⟩

end TwistedConj

end RelSh2

namespace RelSh2

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Homotopy
variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* Γ) (S : Finset Nat.Primes) (A : Rep.{0} k G) (c : G)

def conjHom : G →* G := (MulAut.conj c⁻¹).toMonoidHom

@[scoped simp] lemma conjHom_apply (x : G) : conjHom c x = c⁻¹ * x * c := by
  simp [conjHom]

lemma conjHom_level (x : G) : r (conjHom c x) = (r c)⁻¹ * r x * r c := by
  rw [conjHom_apply, map_mul, map_mul, map_inv]

lemma conj_hφ (g : G) (a : A) : A.ρ c (A.ρ (conjHom c g) a) = A.ρ g (A.ρ c a) := by
  rw [conjHom_apply, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 1; group

noncomputable abbrev conjStar : (G × G → A) →ₗ[k] (G × G → A) := cochainsPullPush₂ (conjHom c) (A.ρ c)

lemma conjStar_apply (z : G × G → A) (x y : G) : conjStar A c z (x, y) = A.ρ c (z (c⁻¹ * x * c, c⁻¹ * y * c)) := by
  simp [cochainsPullPush₂_apply]

def hb (z : G × G → A) : G → A := fun x => z (c, c⁻¹ * x * c) - z (x, c)

lemma conjStar_sub_eq_d (z : G × G → A) (hz : z ∈ cocycles₂ A) : conjStar A c z - z = (d₁₂ A).hom (hb A c z) := by
  funext ⟨x, y⟩
  rw [Pi.sub_apply, conjStar_apply, d₁₂_hom_apply]
  simp only [hb, map_sub]
  have C := (mem_cocycles₂_iff z).1 hz
  have e1 := C x c (c⁻¹ * y * c)
  have e2 := C x y c
  have e3 := C c (c⁻¹ * x * c) (c⁻¹ * y * c)
  rw [show c * (c⁻¹ * y * c) = y * c by group] at e1
  rw [show c * (c⁻¹ * x * c) = x * c by group, show c⁻¹ * x * c * (c⁻¹ * y * c) = c⁻¹ * (x * y) * c by group] at e3

  have key : A.ρ c (z (c⁻¹ * x * c, c⁻¹ * y * c)) - z (x, y) =
      (A.ρ x (z (c, c⁻¹ * y * c)) - A.ρ x (z (y, c))) - (z (c, c⁻¹ * (x * y) * c) - z (x * y, c)) + (z (c, c⁻¹ * x * c) - z (x, c)) := by

    have h1 : A.ρ x (z (c, c⁻¹ * y * c)) = z (x * c, c⁻¹ * y * c) + z (x, c) - z (x, y * c) := by rw [e1]; abel
    have h2 : A.ρ x (z (y, c)) = z (x * y, c) + z (x, y) - z (x, y * c) := by rw [e2]; abel
    have h3 : A.ρ c (z (c⁻¹ * x * c, c⁻¹ * y * c)) = z (x * c, c⁻¹ * y * c) + z (c, c⁻¹ * x * c) - z (c, c⁻¹ * (x * y) * c) :=
      eq_sub_of_add_eq e3.symm
    rw [h1, h2, h3]; abel
  rw [key]

lemma hb_mem_levelCochainsSr₁ {z : G × G → A} (hz : IsLevelConstantSr₂ r S z) : IsLevelConstantSr₁ r S (hb A c z) := by
  obtain ⟨F, hF, h⟩ := hz
  obtain ⟨N, hN, hNF, hconj⟩ := exists_normal_level hF
  refine ⟨N, hN, fun g s hs => ?_⟩
  simp only [hb]
  have hs' : r s ∈ F.fixingSubgroup := hNF hs
  have hcs : r (c⁻¹ * s * c) ∈ F.fixingSubgroup := by
    rw [map_mul, map_mul, map_inv]; exact hNF (hconj _ hs (r c))
  congr 1
  · rw [show c⁻¹ * (g * s) * c = (c⁻¹ * g * c) * (c⁻¹ * s * c) by group]
    have := h c (c⁻¹ * g * c) 1 (c⁻¹ * s * c) (by rw [map_one]; exact Subgroup.one_mem _) hcs
    rwa [mul_one] at this
  · have := h g c s 1 hs' (by rw [map_one]; exact Subgroup.one_mem _)
    rwa [mul_one] at this

lemma conjStar_sub_mem_levelCoboundariesSr₂ {z : G × G → A} (hz : z ∈ levelCocyclesSr₂ r S A) :
    conjStar A c z - z ∈ levelCoboundariesSr₂ r S A := by
  rw [mem_levelCocyclesSr₂_iff] at hz
  exact (mem_levelCoboundariesSr₂_iff r S A _).2 ⟨hb A c z, hb_mem_levelCochainsSr₁ r S A c hz.2, (conjStar_sub_eq_d A c z hz.1).symm⟩

end Homotopy

end RelSh2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin.RelSh2"

namespace RelSh2

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

set_option linter.unusedSectionVars false

section Specific
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]

noncomputable def incl : ↥L.fixingSubgroup →* ↥K.fixingSubgroup := Subgroup.inclusion (IntermediateField.fixingSubgroup_antitone hKL)

lemma incl_apply (s : ↥L.fixingSubgroup) : incl K L hKL s = ⟨(s : Γ), IntermediateField.fixingSubgroup_antitone hKL s.2⟩ := rfl

lemma incl_level (s : ↥L.fixingSubgroup) : K.fixingSubgroup.subtype (incl K L hKL s) = L.fixingSubgroup.subtype s := rfl

lemma incl_mem (s : ↥L.fixingSubgroup) : incl K L hKL s ∈ L.fixingSubgroup.subgroupOf K.fixingSubgroup := Subgroup.mem_subgroupOf.2 s.2

noncomputable def pr₁ : cyclotomicQuotientRep K L p →ₗ[ZMod p] ZMod p :=
  Finsupp.lapply (1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)

lemma pr₁_apply (m : cyclotomicQuotientRep K L p) : pr₁ (p := p) K L m = (m : (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p) 1 := rfl

lemma P1_ρ_apply (g : ↥K.fixingSubgroup) (m : cyclotomicQuotientRep K L p) :
    (cyclotomicQuotientRep K L p).ρ g m =
      ((((cycloChar p).comp K.fixingSubgroup.subtype) g : (ZMod p)ˣ) : ZMod p) • Finsupp.mapDomain (g • ·) (m : (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p) := by
  show ((Rep.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)).ρ.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) g m = _
  rw [Representation.twist_apply, LinearMap.smul_apply]
  congr 1

lemma pr₁_ρ (g : ↥K.fixingSubgroup) (m : cyclotomicQuotientRep K L p) :
    pr₁ K L ((cyclotomicQuotientRep K L p).ρ g m) =
      ((((cycloChar p).comp K.fixingSubgroup.subtype) g : (ZMod p)ˣ) : ZMod p) * (m : (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p) ((g⁻¹ : ↥K.fixingSubgroup) : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) := by
  rw [P1_ρ_apply, map_smul, smul_eq_mul, pr₁_apply]
  congr 1
  have : (1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = g • (((g⁻¹ : ↥K.fixingSubgroup) : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)) := by
    rw [Rep.smul_quotient_eq_mul, ← QuotientGroup.mk_mul, mul_inv_cancel, QuotientGroup.mk_one]
  rw [this, Finsupp.mapDomain_apply (MulAction.injective g)]

lemma hpr (s : ↥L.fixingSubgroup) (m : cyclotomicQuotientRep K L p) :
    pr₁ K L ((cyclotomicQuotientRep K L p).ρ (incl K L hKL s) m) = ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)).ρ s (pr₁ K L m) := by
  rw [pr₁_ρ]
  have h1 : (((incl K L hKL s)⁻¹ : ↥K.fixingSubgroup) : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = 1 := by
    rw [QuotientGroup.eq_one_iff]; exact Subgroup.inv_mem _ (incl_mem K L hKL s)
  rw [h1, ← pr₁_apply]
  show _ = (((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).ρ.twist ((cycloChar p).comp L.fixingSubgroup.subtype)) s) (pr₁ K L m)
  rw [Representation.twist_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

lemma pr₁_RT (σ : ↥K.fixingSubgroup) (m : cyclotomicQuotientRep K L p) :
    pr₁ K L ((cyclotomicQuotientRT K L p σ).hom m) = (m : (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p) (σ : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) := by
  rw [pr₁_apply]
  show (Finsupp.mapDomain (· * ((σ : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup))⁻¹) (m : (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p)) 1 = _
  have : (1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = (fun q : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup => q * ((σ : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup))⁻¹) (σ : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) := by simp
  rw [this, Finsupp.mapDomain_apply (mul_left_injective _)]

variable (σ : ↥K.fixingSubgroup)

noncomputable def fL : ↥L.fixingSubgroup →* ↥L.fixingSubgroup where
  toFun s := ⟨((σ : Γ))⁻¹ * s * σ, by
    have h := Subgroup.Normal.conj_mem' (inferInstance : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal) (incl K L hKL s) (incl_mem K L hKL s) σ
    exact Subgroup.mem_subgroupOf.1 h⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by
    show ((σ : Γ))⁻¹ * (s * t) * σ = ((σ : Γ))⁻¹ * s * σ * (((σ : Γ))⁻¹ * t * σ)
    group)

lemma coe_fL (s : ↥L.fixingSubgroup) : ((fL K L hKL σ s : ↥L.fixingSubgroup) : Γ) = ((σ : Γ))⁻¹ * s * σ := rfl

lemma incl_fL (s : ↥L.fixingSubgroup) : incl K L hKL (fL K L hKL σ s) = σ⁻¹ * incl K L hKL s * σ := Subtype.ext rfl

lemma hfL (s : ↥L.fixingSubgroup) : L.fixingSubgroup.subtype (fL K L hKL σ s) = ((σ : Γ))⁻¹ * L.fixingSubgroup.subtype s * (σ : Γ) := rfl

noncomputable def φL : ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)) →ₗ[ZMod p] ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)) := ((cycloChar p (σ : Γ) : (ZMod p)ˣ) : ZMod p) • LinearMap.id

lemma φL_apply (c : ZMod p) : φL (p := p) K L σ c = ((cycloChar p (σ : Γ) : (ZMod p)ˣ) : ZMod p) * c := rfl

lemma μ_ρ_apply (t : ↥L.fixingSubgroup) (c : ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype))) :
    ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)).ρ t c =
      ((cycloChar p (t : Γ) : (ZMod p)ˣ) : ZMod p) * c := by
  show ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).ρ.twist ((cycloChar p).comp L.fixingSubgroup.subtype)) t c = _
  rw [Representation.twist_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

lemma hφL (s : ↥L.fixingSubgroup) (c : ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype))) :
    φL K L σ (((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)).ρ (fL K L hKL σ s) c) =
      ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)).ρ s (φL K L σ c) := by
  rw [μ_ρ_apply, μ_ρ_apply, φL_apply, φL_apply, coe_fL, map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  ring

end Specific
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin.RelSh2"
end RelSh2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin.RelSh2"

namespace RelSh2

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Assembly
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L)
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]

noncomputable abbrev shZ :
    ↥(levelCocyclesSr₂ K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p)) →ₗ[ZMod p]
      ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
        ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype))) :=
  levelCocyclesSr₂Map (incl K L hKL) (incl_level K L hKL) S (pr₁ K L) (hpr K L hKL)

noncomputable abbrev shF : (↥K.fixingSubgroup × ↥K.fixingSubgroup → cyclotomicQuotientRep K L p) →ₗ[ZMod p]
    (↥L.fixingSubgroup × ↥L.fixingSubgroup → ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype))) :=
  cochainsPullPush₂ (incl K L hKL) (pr₁ K L)

noncomputable abbrev conjLF (σ : ↥K.fixingSubgroup) := cochainsPullPush₂ (fL K L hKL σ) (φL (p := p) K L σ)

lemma key_identity (σ : ↥K.fixingSubgroup) (z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → cyclotomicQuotientRep K L p)
    (s t : ↥L.fixingSubgroup) :
    shF K L hKL (fun xy => (cyclotomicQuotientRT K L p σ).hom (z xy)) (s, t) =
      conjLF K L hKL σ (shF K L hKL (conjStar (cyclotomicQuotientRep K L p) σ⁻¹ z)) (s, t) := by
  rw [cochainsPullPush₂_apply, cochainsPullPush₂_apply, cochainsPullPush₂_apply, pr₁_RT]
  show _ = φL K L σ (pr₁ K L (conjStar (cyclotomicQuotientRep K L p) σ⁻¹ z (incl K L hKL (fL K L hKL σ s), incl K L hKL (fL K L hKL σ t))))
  rw [conjStar_apply, incl_fL, incl_fL, inv_inv,
    show σ * (σ⁻¹ * incl K L hKL s * σ) * σ⁻¹ = incl K L hKL s by group,
    show σ * (σ⁻¹ * incl K L hKL t * σ) * σ⁻¹ = incl K L hKL t by group,
    pr₁_ρ, inv_inv, φL_apply, ← mul_assoc, MonoidHom.comp_apply, Subgroup.coe_subtype, ← Units.val_mul, ← map_mul,
    Subgroup.coe_inv, mul_inv_cancel, map_one, Units.val_one, one_mul]

end Assembly
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin.RelSh2"
end RelSh2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin.RelSh2"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 6400000 in
open RelSh2 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex] :
    ∃ Θ : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p) ≃ₗ[ZMod p]
        continuousH2Sr L.fixingSubgroup.subtype S
          ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)),
      (∀ (z : ↥(levelCocyclesSr₂ K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p)))
          (w : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
            ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
        (∀ s t : ↥L.fixingSubgroup,
            (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
              ((z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p)
                (⟨(s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL s.2⟩,
                 ⟨(t : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL t.2⟩))
                (1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)) →
          Θ (continuousH2Srπ K.fixingSubgroup.subtype S _ z) = continuousH2Srπ L.fixingSubgroup.subtype S _ w) ∧
      ∀ (σ : ↥K.fixingSubgroup) (a : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p))
        (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
          ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
        Θ a = continuousH2Srπ L.fixingSubgroup.subtype S _ w →
        (∀ s t s' t' : ↥L.fixingSubgroup,
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹ * s * σ = s' →
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹ * t * σ = t' →
              (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
                ((cycloChar p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : (ZMod p)ˣ) : ZMod p) *
                  (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) →
          Θ (continuousH2SrMapHom S K.fixingSubgroup.subtype (cyclotomicQuotientRT K L p σ) a) =
            continuousH2Srπ L.fixingSubgroup.subtype S _ w' := by
  obtain ⟨Θ, hpin⟩ := groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq (p := p) S K L hKL hL
  refine ⟨Θ, hpin, ?_⟩
  intro σ a w w' hw hw'
  obtain ⟨z, rfl⟩ := continuousH2Srπ_surjective K.fixingSubgroup.subtype S _ a

  have e1 : continuousH2Srπ L.fixingSubgroup.subtype S _ w = continuousH2Srπ L.fixingSubgroup.subtype S _ (shZ S K L hKL z) :=
    hw.symm.trans (hpin z (shZ S K L hKL z) (fun s t => rfl))
  have e2 : Θ (continuousH2SrMapHom S K.fixingSubgroup.subtype (cyclotomicQuotientRT K L p σ)
      (continuousH2Srπ K.fixingSubgroup.subtype S _ z)) =
      continuousH2Srπ L.fixingSubgroup.subtype S _ (shZ S K L hKL
        (levelCocyclesSr₂Map (MonoidHom.id _) (fun _ => rfl) S (cyclotomicQuotientRT K L p σ).hom.toLinearMap
          (fun g a => Rep.hom_comm_apply (cyclotomicQuotientRT K L p σ) g a) z)) := by
    rw [continuousH2SrMapHom_continuousH2Srπ]
    exact hpin _ _ (fun s t => rfl)
  rw [e2]

  apply (Submodule.Quotient.eq _).2
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]
  have m1 : (w.1 - (shZ S K L hKL z).1) ∈ levelCoboundariesSr₂ L.fixingSubgroup.subtype S _ := by
    have := (Submodule.Quotient.eq _).1 e1
    rwa [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub] at this
  have m2 : shF K L hKL (conjStar (cyclotomicQuotientRep K L p) σ⁻¹ z.1) - shF K L hKL z.1 ∈
      levelCoboundariesSr₂ L.fixingSubgroup.subtype S _ := by
    rw [← map_sub]
    exact cochainsPullPush₂_mem_levelCoboundariesSr₂ (incl K L hKL) (incl_level K L hKL) S
      (B := ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))
      (pr₁ (p := p) K L) (hpr (p := p) K L hKL)
      (conjStar_sub_mem_levelCoboundariesSr₂ K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p) σ⁻¹ z.2)
  have hw'F : w'.1 = conjLF K L hKL σ w.1 := by
    funext ⟨s, t⟩
    rw [cochainsPullPush₂_apply, φL_apply]
    exact hw' s t (fL K L hKL σ s) (fL K L hKL σ t) rfl rfl
  have huv : (shZ S K L hKL (levelCocyclesSr₂Map (MonoidHom.id _) (fun _ => rfl) S (cyclotomicQuotientRT K L p σ).hom.toLinearMap
        (fun g a => Rep.hom_comm_apply (cyclotomicQuotientRT K L p σ) g a) z)).1 =
      conjLF K L hKL σ (shF K L hKL (conjStar (cyclotomicQuotientRep K L p) σ⁻¹ z.1)) := by
    funext ⟨s, t⟩
    exact key_identity K L hKL σ z.1 s t
  rw [huv, hw'F, show conjLF K L hKL σ (shF K L hKL (conjStar (cyclotomicQuotientRep K L p) σ⁻¹ z.1)) - conjLF K L hKL σ w.1 =
    conjLF K L hKL σ ((shF K L hKL (conjStar (cyclotomicQuotientRep K L p) σ⁻¹ z.1) - shF K L hKL z.1) -
      (w.1 - shF K L hKL z.1)) by rw [map_sub, map_sub, map_sub]; abel]
  exact pullPush_mem_levelCoboundariesSr₂ L.fixingSubgroup.subtype S (fL K L hKL σ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hfL K L hKL σ) (φL K L σ) (hφL K L hKL σ) (Submodule.sub_mem _ m2 m1)

end S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin
end P2MW
export P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin (solution)
