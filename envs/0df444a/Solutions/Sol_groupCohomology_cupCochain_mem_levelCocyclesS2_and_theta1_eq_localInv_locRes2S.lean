-- Prove2me | solution 1 for groupCohomology.cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8a9b219e-51d8-5638-96a2-9de9effe3da1

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

noncomputable section

namespace P2M
namespace CupLoc

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime]

lemma ofChar_ρ_apply {G : Type} [Group G] (ψ : G →* (ZMod p)ˣ) (g : G) (x : ZMod p) :
    (ofChar (k := ZMod p) ψ).ρ g x = (ψ g : ZMod p) * x := by
  change ((Representation.trivial (ZMod p) G (ZMod p)).twist ψ) g x = _
  rw [Representation.twist_apply_apply, Representation.isTrivial_apply, smul_eq_mul]

lemma isEquivariantBilinear_eval (M : Rep.{0} (ZMod p) Γℚ) :
    Rep.IsEquivariantBilinear M (M.dualTwist (cycloChar p)) (ofChar (k := ZMod p) (cycloChar p))
      (Module.Dual.eval (ZMod p) M :
        M →ₗ[ZMod p] M.dualTwist (cycloChar p) →ₗ[ZMod p] ofChar (k := ZMod p) (cycloChar p)) := by
  intro g m f
  change (((M.dualTwist (cycloChar p)).ρ g f) : Module.Dual (ZMod p) M) (M.ρ g m) = _
  rw [Rep.dualTwist_ρ_apply, ofChar_ρ_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    smul_eq_mul]
  congr 1
  change f (M.ρ g⁻¹ (M.ρ g m)) = f m
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

lemma ρ_apply_eq_of_level {A : Rep.{0} (ZMod p) Γℚ} (g : cocycles₁ A) (U : Subgroup Γℚ) [U.Normal]
    (hg : ∀ t u, u ∈ U → g (t * u) = g t) (u : Γℚ) (hu : u ∈ U) (t : Γℚ) :
    A.ρ u (g t) = g t := by
  have h1 : g u = 0 := by
    have := hg 1 u hu
    rwa [one_mul, cocycles₁_map_one] at this
  have h2 : g (u * t) = g t := by
    have hconj : t⁻¹ * u * t⁻¹⁻¹ ∈ U := Subgroup.Normal.conj_mem inferInstance u hu t⁻¹
    rw [inv_inv] at hconj
    have := hg t (t⁻¹ * u * t) hconj
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at this
  have h3 := (mem_cocycles₁_iff (⇑g)).1 g.2 u t
  rw [h2, h1, add_zero] at h3
  exact h3.symm

section Cup

variable (S : Finset Nat.Primes) (M : Rep.{0} (ZMod p) Γℚ)

abbrev ev : M →ₗ[ZMod p] M.dualTwist (cycloChar p) →ₗ[ZMod p] ofChar (k := ZMod p) (cycloChar p) :=
  (Module.Dual.eval (ZMod p) M :
    M →ₗ[ZMod p] M.dualTwist (cycloChar p) →ₗ[ZMod p] ofChar (k := ZMod p) (cycloChar p))

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable {S M} in
theorem isLevelConstantS₂_cupCochain (f : cocycles₁ M) (hf : IsLevelConstantS₁ S (⇑f))
    (g : cocycles₁ (M.dualTwist (cycloChar p))) (hg : IsLevelConstantS₁ S (⇑g)) :
    IsLevelConstantS₂ S (cupCochain (ev M) (⇑f) (⇑g)) := by
  obtain ⟨Ff, hFf, hcf⟩ := hf
  obtain ⟨Fg, hFg, hcg⟩ := hg
  set F₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := Ff ⊔ Fg with hF₀
  have hF₀S : F₀.IsUnramifiedOutside S := hFf.sup hFg
  set F : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ F₀ (AlgebraicClosure ℚ) with hF
  have hFS : F.IsUnramifiedOutside S := hF₀S.normalClosure
  haveI : FiniteDimensional ℚ F₀ := hF₀S.1
  haveI : IsGalois ℚ F := IsGalois.normalClosure ℚ F₀ (AlgebraicClosure ℚ)
  haveI hN : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).2 inferInstance
  have hle₀ : F₀ ≤ F := IntermediateField.le_normalClosure F₀
  have hUf : F.fixingSubgroup ≤ Ff.fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone ((le_sup_left : Ff ≤ F₀).trans hle₀)
  have hUg : F.fixingSubgroup ≤ Fg.fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone ((le_sup_right : Fg ≤ F₀).trans hle₀)
  refine ⟨F, hFS, fun s t u u' hu hu' => ?_⟩
  simp only [cupCochain_apply]
  rw [hcf s u (hUf hu), hcg t u' (hUg hu'), map_mul, Module.End.mul_apply,
    ρ_apply_eq_of_level g F.fixingSubgroup (fun t u hu => hcg t u (hUg hu)) u hu t]

variable {S M} in

theorem cupCochain_mem_levelCocyclesS₂ (f : cocycles₁ M) (hf : IsLevelConstantS₁ S (⇑f))
    (g : cocycles₁ (M.dualTwist (cycloChar p))) (hg : IsLevelConstantS₁ S (⇑g)) :
    cupCochain (ev M) (⇑f) (⇑g) ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)) := by
  refine (mem_levelCocyclesS₂_iff S _ _).2 ⟨?_, isLevelConstantS₂_cupCochain f hf g hg⟩
  exact (cup (ev M) (isEquivariantBilinear_eval M) f g).2

end Cup

section Loc

variable {G : Type} [Group G] (r : G →* Γℚ) (A : Rep.{0} (ZMod p) Γℚ)

abbrev pull (f : cocycles₁ A) : cocycles₁ (Rep.res r A) :=
  mapCocycles₁ r (𝟙 (Rep.res r A)) f

@[scoped simp] lemma pull_apply (f : cocycles₁ A) (s : G) : pull r A f s = f (r s) := rfl

lemma coe_pull (f : cocycles₁ A) : ⇑(pull r A f) = ⇑f ∘ ⇑r := by
  funext s; simp

lemma isLevelConstant₁_pull {S : Finset Nat.Primes} (f : cocycles₁ A) (hf : IsLevelConstantS₁ S (⇑f)) :
    IsLevelConstant₁ r (⇑(pull r A f)) := by
  rw [coe_pull]
  exact hf.isLevelConstant₁.precomp (rH := MonoidHom.id _) (rG := r) r (fun _ => rfl)

lemma map_H1π (f : cocycles₁ A) :
    (map r (𝟙 (Rep.res r A)) 1).hom ((H1π A).hom f) = (H1π (Rep.res r A)).hom (pull r A f) := by
  simp [pull]

end Loc

section Theta

variable (S : Finset Nat.Primes) (M : Rep.{0} (ZMod p) Γℚ) {G : Type} [Group G] (r : G →* Γℚ)

theorem theta1_eq_inv_locRes₂S
    (inv : continuousH2 r (ofChar (k := ZMod p) ((cycloChar p).comp r)) →ₗ[ZMod p] ZMod p)
    (θ : continuousH1 r (Rep.res r M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 r (Rep.res r (M.dualTwist (cycloChar p)))))
    (hθ : IsTheta1 r
      (Module.Dual.eval (ZMod p) M :
        Rep.res r M →ₗ[ZMod p] Rep.res r (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
          ofChar (k := ZMod p) ((cycloChar p).comp r)) inv θ)
    (f : cocycles₁ M) (hf : IsLevelConstantS₁ S (⇑f))
    (g : cocycles₁ (M.dualTwist (cycloChar p))) (hg : IsLevelConstantS₁ S (⇑g))
    (he : cupCochain (ev M) (⇑f) (⇑g) ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)))
    (z : continuousH1 r (Rep.res r M)) (w : continuousH1 r (Rep.res r (M.dualTwist (cycloChar p))))
    (hz : (z : H1 (Rep.res r M)) = (map r (𝟙 (Rep.res r M)) 1).hom ((H1π M).hom f))
    (hw : (w : H1 (Rep.res r (M.dualTwist (cycloChar p)))) =
      (map r (𝟙 (Rep.res r (M.dualTwist (cycloChar p)))) 1).hom ((H1π (M.dualTwist (cycloChar p))).hom g)) :
    θ z w = inv (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) r
      (continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨_, he⟩)) := by
  have hz' : z = ⟨(H1π (Rep.res r M)).hom (pull r M f),
      H1π_mem_continuousH1 r _ (isLevelConstant₁_pull r M f hf)⟩ :=
    Subtype.ext (hz.trans (map_H1π r M f))
  have hw' : w = ⟨(H1π (Rep.res r (M.dualTwist (cycloChar p)))).hom (pull r _ g),
      H1π_mem_continuousH1 r _ (isLevelConstant₁_pull r _ g hg)⟩ :=
    Subtype.ext (hw.trans (map_H1π r _ g))
  subst hz' hw'
  refine (hθ (pull r M f) (isLevelConstant₁_pull r M f hf) (pull r _ g)
    (isLevelConstant₁_pull r _ g hg)
    (levelCocycles₂Map (rH := MonoidHom.id _) (rG := r) r (fun _ => rfl)
      (LinearMap.id : ofChar (k := ZMod p) (cycloChar p) →ₗ[ZMod p]
        Rep.res r (ofChar (k := ZMod p) (cycloChar p))) (fun _ _ => rfl)
      (levelCocyclesS₂ToLevelCocycles₂ S _ ⟨_, he⟩)) ?_).trans ?_
  · rintro ⟨s, t⟩
    rfl
  · rfl

end Theta

section Vanish

variable (S : Finset Nat.Primes) (M : Rep.{0} (ZMod p) Γℚ) {G : Type} [Group G] (r : G →* Γℚ)

theorem locRes₂S_cup_eq_zero
    (f : cocycles₁ M) (g : cocycles₁ (M.dualTwist (cycloChar p))) (hg : IsLevelConstantS₁ S (⇑g))
    (he : cupCochain (ev M) (⇑f) (⇑g) ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)))
    (h0 : (map r (𝟙 (Rep.res r M)) 1).hom ((H1π M).hom f) = 0) :
    locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) r
      (continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨_, he⟩) = 0 := by
  rw [map_H1π] at h0
  obtain ⟨m, hm⟩ : ∃ m : M, (d₀₁ (Rep.res r M)).hom m = ⇑(pull r M f) := (H1π_eq_zero_iff _).1 h0
  change continuousH2π r (Rep.res r (ofChar (k := ZMod p) (cycloChar p)))
    (levelCocycles₂Map (rH := MonoidHom.id _) (rG := r) r (fun _ => rfl)
      (LinearMap.id : ofChar (k := ZMod p) (cycloChar p) →ₗ[ZMod p]
        Rep.res r (ofChar (k := ZMod p) (cycloChar p))) (fun _ _ => rfl)
      (levelCocyclesS₂ToLevelCocycles₂ S _ ⟨_, he⟩)) = 0
  rw [continuousH2π_eq_zero_iff, mem_levelCoboundaries₂_iff]
  refine ⟨(fun v => ev M m v) ∘ ⇑(pull r _ g), (isLevelConstant₁_pull r _ g hg).comp _, ?_⟩
  funext ⟨s, t⟩
  have hfs : f (r s) = M.ρ (r s) m - m := by
    have := congr_fun hm s
    simpa [d₀₁_hom_apply] using this.symm
  have hev : ev M (M.ρ (r s) m) ((M.dualTwist (cycloChar p)).ρ (r s) (g (r t)))
      = (ofChar (k := ZMod p) (cycloChar p)).ρ (r s) (ev M m (g (r t))) :=
    isEquivariantBilinear_eval M (r s) m (g (r t))
  have hcoc := (mem_cocycles₁_iff (⇑g)).1 g.2 (r s) (r t)
  show (ofChar (k := ZMod p) (cycloChar p)).ρ (r s) (ev M m (g (r t))) - ev M m (g (r (s * t)))
      + ev M m (g (r s))
      = ev M (f (r s)) ((M.dualTwist (cycloChar p)).ρ (r s) (g (r t)))
  rw [hfs, map_sub, LinearMap.sub_apply, hev, map_mul, hcoc, map_add]
  abel

end Vanish

end P2M.CupLoc
p2m_reactivate "P2MW.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S.P2M P2MW.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S.P2M.CupLoc"
p2m_reactivate "P2MW.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S.P2M"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ)
    (θ : ∀ q : ↥S,
      continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ q))
    (f : cocycles₁ M) (hf : IsLevelConstantS₁ S (⇑f))
    (g : cocycles₁ (M.dualTwist (cycloChar p))) (hg : IsLevelConstantS₁ S (⇑g)) :
    ∃ hc : cupCochain (Module.Dual.eval (ZMod p) M :
          M →ₗ[ZMod p] M.dualTwist (cycloChar p) →ₗ[ZMod p] ofChar (k := ZMod p) (cycloChar p))
        (⇑f) (⇑g) ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)),
      (∀ q : ↥S,
        haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
        ∀ (z : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
          (w : continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))),
          (z : H1 _) = (locRes (extArithLoc S) M (Sum.inr q)).hom ((H1π M).hom f) →
          (w : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom
              ((H1π (M.dualTwist (cycloChar p))).hom g) →
          θ q z w = localInv p ζ (q : Nat.Primes)
            (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q))
              (continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨_, hc⟩))) ∧
      ((locRes (extArithLoc S) M (Sum.inl ())).hom ((H1π M).hom f) = 0 →
        locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inl ()))
          (continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨_, hc⟩) = 0) := by
  refine ⟨P2M.CupLoc.cupCochain_mem_levelCocyclesS₂ f hf g hg, fun q => ?_, fun h0 => ?_⟩
  · intro z w hz hw
    haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
    exact P2M.CupLoc.theta1_eq_inv_locRes₂S S M (extArithLoc S (Sum.inr q))
      (localInv p ζ (q : Nat.Primes)) (θ q) (hθ q) f hf g hg _ z w hz hw
  · exact P2M.CupLoc.locRes₂S_cup_eq_zero S M (extArithLoc S (Sum.inl ())) f g hg _ h0

end
p2m_reactivate "P2MW.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S.P2M P2MW.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S.P2M.CupLoc"

end S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S
end P2MW
export P2MW.S_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S (solution)
