-- Prove2me | solution 1 for groupCohomology.bijective_theta_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4ddb9a0c-de45-50e6-9edc-cb35bf3568a9

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_theta_of_mulEquiv

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory groupCohomology

theorem solution
    {k G₁ G₂ : Type u} [CommRing k] [Group G₁] [Group G₂]
    (r₁ : G₁ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (r₂ : G₂ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (e : G₂ ≃* G₁) (he : ∀ g : G₂, r₁ (e.toMonoidHom g) = r₂ g)
    {M D N : Rep.{u} k G₁} (φ : M →ₗ[k] D →ₗ[k] N)
    (inv₂ : continuousH2 r₂ (Rep.res e.toMonoidHom N) →ₗ[k] k) (hinv₂ : Function.Bijective inv₂)
    (hG₁ : Function.Bijective (inv₂ ∘ₗ continuousH2Map (rH := r₁) (rG := r₂) (A := N) (B := Rep.res e.toMonoidHom N)
          e.toMonoidHom he LinearMap.id (fun _ _ => rfl)) →
      ∀ (θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r₁ D)),
        IsTheta0 r₁ φ (inv₂ ∘ₗ continuousH2Map (rH := r₁) (rG := r₂) (A := N) (B := Rep.res e.toMonoidHom N)
          e.toMonoidHom he LinearMap.id (fun _ _ => rfl)) θ₀ →
      ∀ (θ₁ : continuousH1 r₁ M →ₗ[k] Module.Dual k (continuousH1 r₁ D)),
        IsTheta1 r₁ φ (inv₂ ∘ₗ continuousH2Map (rH := r₁) (rG := r₂) (A := N) (B := Rep.res e.toMonoidHom N)
          e.toMonoidHom he LinearMap.id (fun _ _ => rfl)) θ₁ →
      ∀ (θ₂ : continuousH2 r₁ M →ₗ[k] Module.Dual k D.ρ.invariants),
        IsTheta2 r₁ φ (inv₂ ∘ₗ continuousH2Map (rH := r₁) (rG := r₂) (A := N) (B := Rep.res e.toMonoidHom N)
          e.toMonoidHom he LinearMap.id (fun _ _ => rfl)) θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (Θ₀ : (Rep.res e.toMonoidHom M).ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r₂ (Rep.res e.toMonoidHom D)))
    (hΘ₀ : IsTheta0 r₂ (φ : Rep.res e.toMonoidHom M →ₗ[k] Rep.res e.toMonoidHom D →ₗ[k] Rep.res e.toMonoidHom N) inv₂ Θ₀)
    (Θ₁ : continuousH1 r₂ (Rep.res e.toMonoidHom M) →ₗ[k] Module.Dual k (continuousH1 r₂ (Rep.res e.toMonoidHom D)))
    (hΘ₁ : IsTheta1 r₂ (φ : Rep.res e.toMonoidHom M →ₗ[k] Rep.res e.toMonoidHom D →ₗ[k] Rep.res e.toMonoidHom N) inv₂ Θ₁)
    (Θ₂ : continuousH2 r₂ (Rep.res e.toMonoidHom M) →ₗ[k] Module.Dual k (Rep.res e.toMonoidHom D).ρ.invariants)
    (hΘ₂ : IsTheta2 r₂ (φ : Rep.res e.toMonoidHom M →ₗ[k] Rep.res e.toMonoidHom D →ₗ[k] Rep.res e.toMonoidHom N) inv₂ Θ₂) :
    Function.Bijective Θ₀ ∧ Function.Bijective Θ₁ ∧ Function.Bijective Θ₂ := by
  classical

  have retract : ∀ {X Y X₁ Y₁ : Type u} (f : X → Y) (F : X₁ → Y₁) (ι : X → X₁) (p : X₁ → X) (j : Y → Y₁) (q : Y₁ → Y),
      (∀ x, p (ι x) = x) → (∀ y, q (j y) = y) → (∀ x, F (ι x) = j (f x)) → (∀ x₁, f (p x₁) = q (F x₁)) →
      Function.Bijective F → Function.Bijective f := by
    intro X Y X₁ Y₁ f F ι p j q hp hq h1 h2 hF
    refine ⟨fun x x' hxx' => ?_, fun y => ?_⟩
    · have : ι x = ι x' := hF.1 (by rw [h1, h1, hxx'])
      rw [← hp x, ← hp x', this]
    · obtain ⟨x₁, hx₁⟩ := hF.2 (j y)
      exact ⟨p x₁, by rw [h2, hx₁, hq]⟩

  let f : G₂ →* G₁ := e.toMonoidHom
  have he' : ∀ g : G₁, r₂ (e.symm.toMonoidHom g) = r₁ g := fun g => by
    rw [← he]; show r₁ (e (e.symm g)) = r₁ g; rw [e.apply_symm_apply]
  have hee : ∀ g : G₁, f (e.symm.toMonoidHom g) = g := fun g => e.apply_symm_apply g
  have hee' : ∀ g : G₂, e.symm.toMonoidHom (f g) = g := fun g => e.symm_apply_apply g

  let P0 : ∀ X : Rep.{u} k G₁, X.ρ.invariants →ₗ[k] (Rep.res f X).ρ.invariants := fun X =>
    { toFun := fun x => ⟨x, fun g => x.2 (f g)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Q0 : ∀ X : Rep.{u} k G₁, (Rep.res f X).ρ.invariants →ₗ[k] X.ρ.invariants := fun X =>
    { toFun := fun y => ⟨y, fun g => by have := y.2 (e.symm.toMonoidHom g); rwa [show (Rep.res f X).ρ (e.symm.toMonoidHom g) = X.ρ g by
          show X.ρ (f (e.symm.toMonoidHom g)) = X.ρ g; rw [hee]] at this⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hQP0 : ∀ (X : Rep.{u} k G₁) x, Q0 X (P0 X x) = x := fun _ _ => rfl
  have hPQ0 : ∀ (X : Rep.{u} k G₁) y, P0 X (Q0 X y) = y := fun _ _ => rfl
  have coe_P0 : ∀ (X : Rep.{u} k G₁) (x : X.ρ.invariants), ((P0 X x : (Rep.res f X).ρ.invariants) : X) = x := fun _ _ => rfl
  have coe_Q0 : ∀ (X : Rep.{u} k G₁) (y : (Rep.res f X).ρ.invariants), ((Q0 X y : X.ρ.invariants) : X) = y := fun _ _ => rfl

  let lcP : ∀ X : Rep.{u} k G₁, levelCocycles₂ r₁ X →ₗ[k] levelCocycles₂ r₂ (Rep.res f X) := fun X =>
    levelCocycles₂Map (rH := r₁) (rG := r₂) (A := X) (B := Rep.res f X) f he LinearMap.id (fun _ _ => rfl)
  have coe_lcP : ∀ (X : Rep.{u} k G₁) (z : levelCocycles₂ r₁ X) st,
      (lcP X z : G₂ × G₂ → X) st = (z : G₁ × G₁ → X) (f st.1, f st.2) := fun _ _ _ => rfl
  let lcQ : ∀ X : Rep.{u} k G₁, levelCocycles₂ r₂ (Rep.res f X) →ₗ[k] levelCocycles₂ r₁ X := fun X =>
    levelCocycles₂Map (rH := r₂) (rG := r₁) (A := Rep.res f X) (B := X) e.symm.toMonoidHom he' LinearMap.id (fun g x => by
      show X.ρ (f (e.symm.toMonoidHom g)) x = X.ρ g x; rw [hee])
  have coe_lcQ : ∀ (X : Rep.{u} k G₁) (z : levelCocycles₂ r₂ (Rep.res f X)) st,
      (lcQ X z : G₁ × G₁ → X) st = (z : G₂ × G₂ → X) (e.symm.toMonoidHom st.1, e.symm.toMonoidHom st.2) := fun _ _ _ => rfl
  let P2 : ∀ X : Rep.{u} k G₁, continuousH2 r₁ X →ₗ[k] continuousH2 r₂ (Rep.res f X) := fun X =>
    continuousH2Map (rH := r₁) (rG := r₂) (A := X) (B := Rep.res f X) f he LinearMap.id (fun _ _ => rfl)
  let Q2 : ∀ X : Rep.{u} k G₁, continuousH2 r₂ (Rep.res f X) →ₗ[k] continuousH2 r₁ X := fun X =>
    continuousH2Map (rH := r₂) (rG := r₁) (A := Rep.res f X) (B := X) e.symm.toMonoidHom he' LinearMap.id (fun g x => by
      show X.ρ (f (e.symm.toMonoidHom g)) x = X.ρ g x; rw [hee])
  have P2_π : ∀ (X : Rep.{u} k G₁) z, P2 X (continuousH2π r₁ X z) = continuousH2π r₂ _ (lcP X z) := fun _ _ => rfl
  have Q2_π : ∀ (X : Rep.{u} k G₁) z, Q2 X (continuousH2π r₂ _ z) = continuousH2π r₁ X (lcQ X z) := fun _ _ => rfl
  have hQP2 : ∀ (X : Rep.{u} k G₁) x, Q2 X (P2 X x) = x := by
    intro X x
    induction x using Submodule.Quotient.induction_on with | _ z =>
    show Q2 X (P2 X (continuousH2π r₁ X z)) = continuousH2π r₁ X z
    rw [P2_π, Q2_π]; congr 1
    apply Subtype.ext; funext st
    rw [coe_lcQ, coe_lcP]
    show (z : G₁ × G₁ → X) (f (e.symm.toMonoidHom st.1), f (e.symm.toMonoidHom st.2)) = (z : G₁ × G₁ → X) st
    rw [hee, hee]
  have hPQ2 : ∀ (X : Rep.{u} k G₁) y, P2 X (Q2 X y) = y := by
    intro X y
    induction y using Submodule.Quotient.induction_on with | _ z =>
    show P2 X (Q2 X (continuousH2π r₂ _ z)) = continuousH2π r₂ _ z
    rw [Q2_π, P2_π]; congr 1
    apply Subtype.ext; funext st
    rw [coe_lcP, coe_lcQ]
    show (z : G₂ × G₂ → X) (e.symm.toMonoidHom (f st.1), e.symm.toMonoidHom (f st.2)) = (z : G₂ × G₂ → X) st
    rw [hee', hee']

  have H1map : ∀ {G H : Type u} [Group G] [Group H] {A : Rep.{u} k H} {B : Rep.{u} k G} (g : G →* H) (ψ : Rep.res g A ⟶ B) (x : cocycles₁ A),
      (map g ψ 1).hom ((H1π A).hom x) = (H1π B).hom (mapCocycles₁ g ψ x) := fun g ψ x => H1π_comp_map_apply g ψ x
  let ψQ : ∀ X : Rep.{u} k G₁, Rep.res e.symm.toMonoidHom (Rep.res f X) ⟶ X := fun X =>
    Rep.ofHom (LinearMap.id.intertwiningMap_of_isIntertwiningMap (Rep.res e.symm.toMonoidHom (Rep.res f X)).ρ X.ρ (fun g x => by
      show X.ρ (f (e.symm.toMonoidHom g)) x = X.ρ g x; rw [hee]))
  let P1 : ∀ X : Rep.{u} k G₁, continuousH1 r₁ X →ₗ[k] continuousH1 r₂ (Rep.res f X) := fun X =>
    ((map f (𝟙 (Rep.res f X)) 1).hom ∘ₗ (continuousH1 r₁ X).subtype).codRestrict _ fun x => by
      obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff r₁ X _).1 x.2
      show (map f (𝟙 (Rep.res f X)) 1).hom (x : H1 X) ∈ continuousH1 r₂ (Rep.res f X)
      rw [← hx, H1map]
      refine H1π_mem_continuousH1 r₂ _ ?_
      obtain ⟨F, hF, h⟩ := hc
      exact ⟨F, hF, fun g s hs => by
        show (c : G₁ → X) (f (g * s)) = (c : G₁ → X) (f g)
        rw [map_mul]; exact h (f g) (f s) (by rw [he]; exact hs)⟩
  let Q1 : ∀ X : Rep.{u} k G₁, continuousH1 r₂ (Rep.res f X) →ₗ[k] continuousH1 r₁ X := fun X =>
    ((map e.symm.toMonoidHom (ψQ X) 1).hom ∘ₗ (continuousH1 r₂ (Rep.res f X)).subtype).codRestrict _ fun x => by
      obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff r₂ _ _).1 x.2
      show (map e.symm.toMonoidHom (ψQ X) 1).hom (x : H1 (Rep.res f X)) ∈ continuousH1 r₁ X
      rw [← hx, H1map]
      refine H1π_mem_continuousH1 r₁ _ ?_
      obtain ⟨F, hF, h⟩ := hc
      exact ⟨F, hF, fun g s hs => by
        show (c : G₂ → X) (e.symm.toMonoidHom (g * s)) = (c : G₂ → X) (e.symm.toMonoidHom g)
        rw [map_mul]; exact h _ _ (by rw [he']; exact hs)⟩
  have P1_mk : ∀ (X : Rep.{u} k G₁) (c : cocycles₁ X) (hc : IsLevelConstant₁ r₁ c),
      ∃ hc' : IsLevelConstant₁ r₂ (mapCocycles₁ f (𝟙 (Rep.res f X)) c),
        P1 X ⟨(H1π X).hom c, H1π_mem_continuousH1 r₁ X hc⟩
          = ⟨(H1π _).hom (mapCocycles₁ f (𝟙 (Rep.res f X)) c), H1π_mem_continuousH1 r₂ _ hc'⟩ := by
    intro X c hc
    have hval : (P1 X ⟨(H1π X).hom c, H1π_mem_continuousH1 r₁ X hc⟩ : H1 (Rep.res f X)) = (H1π _).hom (mapCocycles₁ f (𝟙 (Rep.res f X)) c) :=
      H1map f _ c
    have hmem := (P1 X ⟨(H1π X).hom c, H1π_mem_continuousH1 r₁ X hc⟩).2
    rw [hval] at hmem
    obtain ⟨c', hc', hcc'⟩ := (mem_continuousH1_iff r₂ _ _).1 hmem
    obtain ⟨F, hF, h⟩ := hc
    refine ⟨⟨F, hF, fun g s hs => by
        show (c : G₁ → X) (f (g * s)) = (c : G₁ → X) (f g)
        rw [map_mul]; exact h (f g) (f s) (by rw [he]; exact hs)⟩, Subtype.ext hval⟩
  have Q1_mk : ∀ (X : Rep.{u} k G₁) (c : cocycles₁ (Rep.res f X)) (hc : IsLevelConstant₁ r₂ c),
      ∃ hc' : IsLevelConstant₁ r₁ (mapCocycles₁ e.symm.toMonoidHom (ψQ X) c),
        Q1 X ⟨(H1π _).hom c, H1π_mem_continuousH1 r₂ _ hc⟩
          = ⟨(H1π X).hom (mapCocycles₁ e.symm.toMonoidHom (ψQ X) c), H1π_mem_continuousH1 r₁ X hc'⟩ := by
    intro X c hc
    have hval : (Q1 X ⟨(H1π _).hom c, H1π_mem_continuousH1 r₂ _ hc⟩ : H1 X) = (H1π X).hom (mapCocycles₁ e.symm.toMonoidHom (ψQ X) c) :=
      H1map e.symm.toMonoidHom _ c
    obtain ⟨F, hF, h⟩ := hc
    refine ⟨⟨F, hF, fun g s hs => by
        show (c : G₂ → X) (e.symm.toMonoidHom (g * s)) = (c : G₂ → X) (e.symm.toMonoidHom g)
        rw [map_mul]; exact h _ _ (by rw [he']; exact hs)⟩, Subtype.ext hval⟩
  have exists_rep : ∀ {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A : Rep.{u} k G} (x : continuousH1 r A),
      ∃ c : cocycles₁ A, ∃ hc : IsLevelConstant₁ r c, x = ⟨(H1π A).hom c, H1π_mem_continuousH1 r A hc⟩ := by
    intro G _ r A x
    obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff r A _).1 x.2
    exact ⟨c, hc, Subtype.ext hx.symm⟩
  have hQP1 : ∀ (X : Rep.{u} k G₁) x, Q1 X (P1 X x) = x := by
    intro X x
    obtain ⟨c, hc, rfl⟩ := exists_rep r₁ x
    obtain ⟨hc', hP⟩ := P1_mk X c hc
    rw [hP]
    obtain ⟨hc'', hQ⟩ := Q1_mk X _ hc'
    rw [hQ]
    apply Subtype.ext
    show (H1π X).hom _ = (H1π X).hom c
    congr 1
    apply cocycles₁_ext; intro g
    show (c : G₁ → X) (f (e.symm.toMonoidHom g)) = c g
    rw [hee]
  have hPQ1 : ∀ (X : Rep.{u} k G₁) y, P1 X (Q1 X y) = y := by
    intro X y
    obtain ⟨c, hc, rfl⟩ := exists_rep r₂ y
    obtain ⟨hc', hQ⟩ := Q1_mk X c hc
    rw [hQ]
    obtain ⟨hc'', hP⟩ := P1_mk X _ hc'
    rw [hP]
    apply Subtype.ext
    show (H1π _).hom _ = (H1π _).hom c
    congr 1
    apply cocycles₁_ext; intro g
    show (c : G₂ → X) (e.symm.toMonoidHom (f g)) = c g
    rw [hee']

  let θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r₁ D) :=
    (P2 D).dualMap ∘ₗ Θ₀ ∘ₗ P0 M
  let θ₁ : continuousH1 r₁ M →ₗ[k] Module.Dual k (continuousH1 r₁ D) :=
    (P1 D).dualMap ∘ₗ Θ₁ ∘ₗ P1 M
  let θ₂ : continuousH2 r₁ M →ₗ[k] Module.Dual k D.ρ.invariants :=
    (P0 D).dualMap ∘ₗ Θ₂ ∘ₗ P2 M
  have hθ₀ : IsTheta0 r₁ φ (inv₂ ∘ₗ P2 N) θ₀ := by
    intro m z w hw
    show Θ₀ (P0 M m) (P2 D (continuousH2π r₁ D z)) = inv₂ (P2 N (continuousH2π r₁ N w))
    rw [P2_π, P2_π]
    exact hΘ₀ (P0 M m) (lcP D z) (lcP N w) (fun st => by rw [coe_lcP, coe_lcP, coe_P0]; exact hw _)
  have hθ₁ : IsTheta1 r₁ φ (inv₂ ∘ₗ P2 N) θ₁ := by
    intro c hc g hg w hw
    obtain ⟨hc', hPc⟩ := P1_mk M c hc
    obtain ⟨hg', hPg⟩ := P1_mk D g hg
    show Θ₁ (P1 M _) (P1 D _) = inv₂ (P2 N (continuousH2π r₁ N w))
    rw [hPc, hPg, P2_π]
    refine hΘ₁ _ hc' _ hg' (lcP N w) (fun st => ?_)
    rw [coe_lcP, hw]
    rfl
  have hθ₂ : IsTheta2 r₁ φ (inv₂ ∘ₗ P2 N) θ₂ := by
    intro z d w hw
    show Θ₂ (P2 M (continuousH2π r₁ M z)) (P0 D d) = inv₂ (P2 N (continuousH2π r₁ N w))
    rw [P2_π, P2_π]
    exact hΘ₂ (lcP M z) (P0 D d) (lcP N w) (fun st => by rw [coe_lcP, coe_lcP, coe_P0]; exact hw _)
  have hbijinv : Function.Bijective (inv₂ ∘ₗ P2 N) :=
    hinv₂.comp ⟨fun x y hxy => by rw [← hQP2 N x, ← hQP2 N y]; exact congrArg _ hxy,
      fun y => ⟨Q2 N y, hPQ2 N y⟩⟩
  obtain ⟨hb0, hb1, hb2⟩ := hG₁ hbijinv θ₀ hθ₀ θ₁ hθ₁ θ₂ hθ₂

  refine ⟨?_, ?_, ?_⟩
  · refine retract Θ₀ θ₀ (Q0 M) (P0 M) (P2 D).dualMap (Q2 D).dualMap (hPQ0 M) ?_ ?_ ?_ hb0
    · intro ψ; apply LinearMap.ext; intro w₂
      show ψ (P2 D (Q2 D w₂)) = ψ w₂; rw [hPQ2]
    · intro y; apply LinearMap.ext; intro w
      show Θ₀ (P0 M (Q0 M y)) (P2 D w) = Θ₀ y (P2 D w); rw [hPQ0]
    · intro m; apply LinearMap.ext; intro w₂
      show Θ₀ (P0 M m) w₂ = Θ₀ (P0 M m) (P2 D (Q2 D w₂)); rw [hPQ2]
  · refine retract Θ₁ θ₁ (Q1 M) (P1 M) (P1 D).dualMap (Q1 D).dualMap (hPQ1 M) ?_ ?_ ?_ hb1
    · intro ψ; apply LinearMap.ext; intro y₂
      show ψ (P1 D (Q1 D y₂)) = ψ y₂; rw [hPQ1]
    · intro y; apply LinearMap.ext; intro w
      show Θ₁ (P1 M (Q1 M y)) (P1 D w) = Θ₁ y (P1 D w); rw [hPQ1]
    · intro x; apply LinearMap.ext; intro y₂
      show Θ₁ (P1 M x) y₂ = Θ₁ (P1 M x) (P1 D (Q1 D y₂)); rw [hPQ1]
  · refine retract Θ₂ θ₂ (Q2 M) (P2 M) (P0 D).dualMap (Q0 D).dualMap (hPQ2 M) ?_ ?_ ?_ hb2
    · intro ψ; apply LinearMap.ext; intro d₂
      show ψ (P0 D (Q0 D d₂)) = ψ d₂; rw [hPQ0]
    · intro y; apply LinearMap.ext; intro d
      show Θ₂ (P2 M (Q2 M y)) (P0 D d) = Θ₂ y (P0 D d); rw [hPQ2]
    · intro x; apply LinearMap.ext; intro d₂
      show Θ₂ (P2 M x) d₂ = Θ₂ (P2 M x) (P0 D (Q0 D d₂)); rw [hPQ0]

end S_groupCohomology_bijective_theta_of_mulEquiv
end P2MW
export P2MW.S_groupCohomology_bijective_theta_of_mulEquiv (solution)
