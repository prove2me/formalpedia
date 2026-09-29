-- Prove2me | solution 1 for groupCohomology.isLocalBridge2_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f2776634-1d79-5872-8131-4fb3c07a9573

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_isLocalBridge2_injective

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace LB1EX

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
  {R P B : Rep.{0} k D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep.{0} k D} {A : Rep.{0} k H} (ι : X →+ A)
  {p : ℕ} {M : Rep.{0} (ZMod p) H} (κ : B →+ M →+ A)

def homAdd {V W : Rep.{0} k D} (χ : V ⟶ W) : V →+ W := χ.hom.toLinearMap.toAddMonoidHom

lemma homAdd_apply {V W : Rep.{0} k D} (χ : V ⟶ W) (v : V) : homAdd χ v = χ.hom v := rfl

def homOfLinear {V W : Rep.{0} k D} (L : V →ₗ[k] W) (hL : ∀ (d : D) (v : V), L (V.ρ d v) = W.ρ d (L v)) : V ⟶ W :=
  Rep.ofHom ⟨L, fun d => LinearMap.ext (hL d)⟩

lemma homOfLinear_hom_apply {V W : Rep.{0} k D} (L : V →ₗ[k] W) (hL : ∀ (d : D) (v : V), L (V.ρ d v) = W.ρ d (L v)) (v : V) :
    (homOfLinear L hL).hom v = L v := rfl

def ev (ψ : (ihom (Rep.res π P)).obj A) : P →+ A := LinearMap.toAddMonoidHom (show P →ₗ[k] A from ψ)

lemma ev_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ + ψ') x = ev π ψ x + ev π ψ' x := rfl
lemma ev_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ - ψ') x = ev π ψ x - ev π ψ' x := rfl

noncomputable def cob (ψ : (ihom (Rep.res π P)).obj A) (h : H) : P →+ A := ev π ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom ψ h)

lemma cob_apply (ψ : (ihom (Rep.res π P)).obj A) (h : H) (x : P) :
    cob π ψ h x = A.ρ h (ev π ψ (P.ρ (π h⁻¹) x)) - ev π ψ x := by
  change ev π (((ihom (Rep.res π P)).obj A).ρ h ψ - ψ) x = _
  rw [ev_sub]
  congr 1

lemma cob_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : cob π (ψ + ψ') h x = cob π ψ h x + cob π ψ' h x := by
  simp only [cob, map_add, Pi.add_apply, ev_add]

lemma cob_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : cob π (ψ - ψ') h x = cob π ψ h x - cob π ψ' h x := by
  simp only [cob, map_sub, Pi.sub_apply, ev_sub]

lemma ρ_ρ_inv {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d (V.ρ d⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma ρ_one_apply {V : Rep.{0} k D} (v : V) : V.ρ 1 v = v := by
  rw [map_one, Module.End.one_apply]

lemma ρ_inv_ρ {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d⁻¹ (V.ρ d v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

section hyps

variable (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
  (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
  (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
  (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)

include hκ in

lemma κ_inj {m m' : M} (h : ∀ b, κ b m = κ b m') : m = m' :=
  (hκ (κ.flip m')).unique h (fun _ => rfl)

include hfg hg hκ in

lemma exists_forall_κ_eq (c : P →+ A) (hc : ∀ x : R, c (f.hom x) = 0) : ∃ m : M, ∀ x : P, κ (g.hom x) m = c x := by
  classical

  have hker : ∀ y y' : P, g.hom y = g.hom y' → c y = c y' := by
    intro y y' hyy'
    have h0 : g.hom (y - y') = 0 := by rw [map_sub, hyy', sub_self]
    obtain ⟨x, hx⟩ := (hfg _).1 h0
    have := hc x
    rw [hx, map_sub, sub_eq_zero] at this
    exact this
  let s : B → P := Function.surjInv hg
  have hs : ∀ b, g.hom (s b) = b := Function.surjInv_eq hg
  let cB : B →+ A :=
    { toFun := fun b => c (s b)
      map_zero' := by rw [hker (s 0) 0 (by rw [hs, map_zero]), map_zero]
      map_add' := fun b b' => by rw [← map_add, hker (s (b + b')) (s b + s b') (by rw [hs, map_add, hs, hs])] }
  obtain ⟨m, hm, -⟩ := hκ cB
  exact ⟨m, fun x => by rw [hm]; exact hker _ _ (hs _)⟩

include hιeq in

lemma cob_apply_f (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A)
    (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : R) : cob π ψ h (f.hom x) = 0 := by
  rw [cob_apply, ← Rep.hom_comm_apply f, hψ, hψ, Rep.hom_comm_apply φ, ← hιeq, map_inv, ρ_ρ_inv, sub_self]

include hκeq in

lemma κ_ρ (h : H) (b : B) (m : M) : κ b (M.ρ h m) = A.ρ h (κ (B.ρ (π h⁻¹) b) m) := by
  rw [← hκeq, map_inv, ρ_ρ_inv]

noncomputable def nOf (ψ : (ihom (Rep.res π P)).obj A) (h : H) : M := by
  classical
  exact if hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x then hex.choose else 0

include hfg hg hκ hιeq in
lemma κ_nOf (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : P) :
    κ (g.hom x) (nOf π g κ ψ h) = cob π ψ h x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x :=
    exists_forall_κ_eq f g κ hfg hg hκ (cob π ψ h) (cob_apply_f π f ι hιeq φ ψ hψ h)
  simp only [nOf, dif_pos hex]
  exact hex.choose_spec x

include hg hκ hκeq in

lemma mem_cocycles₁_of_forall_κ (ψ : (ihom (Rep.res π P)).obj A) (n : H → M)
    (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) : n ∈ cocycles₁ M := by
  rw [mem_cocycles₁_iff]
  intro h₁ h₂
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [map_add, hn, κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hn, hn]
  simp only [cob_apply, map_mul, mul_inv_rev, Module.End.mul_apply, map_sub]
  abel

include hg hκ hκeq in

lemma sub_mem_coboundaries₁ (ψ ψ' : (ihom (Rep.res π P)).obj A) (n n' : H → M)
    (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) (hn' : ∀ (h : H) (x : P), κ (g.hom x) (n' h) = cob π ψ' h x)
    (m₀ : M) (hm₀ : ∀ x : P, κ (g.hom x) m₀ = ev π (ψ - ψ') x) : n - n' ∈ coboundaries₁ M := by
  refine ⟨m₀, funext fun h => ?_⟩
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [d₀₁_hom_apply, Pi.sub_apply, map_sub, map_sub, hn, hn', κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hm₀, hm₀, ← cob_sub,
    cob_apply]

include hιeq in

lemma cob_eq_zero_of_hom (χ : P ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : P, ev π ψ x = ι (χ.hom x)) (h : H) (x : P) :
    cob π ψ h x = 0 := by
  rw [cob_apply, hψ, hψ, Rep.hom_comm_apply χ, ← hιeq, map_inv, ρ_ρ_inv, sub_self]

include hκeq in

lemma cob_of_κ (m₀ : M) (θ : (ihom (Rep.res π P)).obj A) (hθ : ∀ x : P, ev π θ x = κ (g.hom x) m₀) (h : H) (x : P) :
    cob π θ h x = κ (g.hom x) (M.ρ h m₀) - κ (g.hom x) m₀ := by
  rw [cob_apply, hθ, hθ, Rep.hom_comm_apply g, ← κ_ρ π κ hκeq]

lemma ρ_ev_of_cob_eq_zero (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ (h : H) (x : P), cob π ψ h x = 0) (h : H) (x : P) :
    A.ρ h (ev π ψ x) = ev π ψ (P.ρ (π h) x) := by
  have := hψ h (P.ρ (π h) x)
  rw [cob_apply, sub_eq_zero, map_inv, ρ_inv_ρ] at this
  exact this

lemma ρ_ev_of_cob_eq_zero_of_ker (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ (h : H) (x : P), cob π ψ h x = 0) (s : H)
    (hs : π s = 1) (x : P) : A.ρ s (ev π ψ x) = ev π ψ x := by
  rw [ρ_ev_of_cob_eq_zero π ψ hψ, hs, map_one, Module.End.one_apply]

lemma ev_ext {s t : (ihom (Rep.res π P)).obj A} (hst : ∀ x : P, ev π s x = ev π t x) : s = t := LinearMap.ext hst

lemma ev_ρ (h : H) (t : (ihom (Rep.res π P)).obj A) (x : P) :
    ev π (((ihom (Rep.res π P)).obj A).ρ h t) x = A.ρ h (ev π t (P.ρ (π h⁻¹) x)) := rfl

include hg hκ in

lemma isLevelConstant₁_of_forall_κ (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    (ψ : (ihom (Rep.res π P)).obj A)
    (hψlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (ev π ψ x) = ev π ψ x)
    (n : H → M) (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) : IsLevelConstant₁ r n := by
  obtain ⟨F₁, hF₁, h₁⟩ := hπlev
  obtain ⟨F₂, hF₂, h₂⟩ := hψlev
  haveI := hF₁
  haveI := hF₂
  refine ⟨F₁ ⊔ F₂, inferInstance, fun h s hs => ?_⟩
  have hs₁ : π s = 1 := h₁ s (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
  have hs₂ := h₂ s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [hn, hn, cob_apply, cob_apply, mul_inv_rev, map_mul π, map_inv π s, hs₁, inv_one, one_mul, map_mul, Module.End.mul_apply,
    hs₂]

def evD {V W : Rep.{0} k D} (t : (ihom V).obj W) : V →+ W := LinearMap.toAddMonoidHom (show V →ₗ[k] W from t)

lemma evD_add {V W : Rep.{0} k D} (s t : (ihom V).obj W) (x : V) : evD (s + t) x = evD s x + evD t x := rfl
lemma evD_sub {V W : Rep.{0} k D} (s t : (ihom V).obj W) (x : V) : evD (s - t) x = evD s x - evD t x := rfl
lemma evD_zero {V W : Rep.{0} k D} (x : V) : evD (0 : (ihom V).obj W) x = 0 := rfl
lemma evD_ρ {V W : Rep.{0} k D} (d : D) (t : (ihom V).obj W) (x : V) :
    evD (((ihom V).obj W).ρ d t) x = W.ρ d (evD t (V.ρ d⁻¹ x)) := rfl

lemma cocycle_evD (a : D → (ihom R).obj X) (ha : a ∈ cocycles₁ ((ihom R).obj X)) (d₁ d₂ : D) (x : R) :
    X.ρ d₁ (evD (a d₂) (R.ρ d₁⁻¹ x)) - evD (a (d₁ * d₂)) x + evD (a d₁) x = 0 := by
  have h := (mem_cocycles₁_iff a).1 ha d₁ d₂
  have := congrArg (fun t => evD t x) h
  simp only [evD_add, evD_ρ] at this
  rw [this]
  abel

noncomputable def cob₂ (Φ : H → (ihom (Rep.res π P)).obj A) (g₁ g₂ : H) : P →+ A := ev π ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom Φ (g₁, g₂))

lemma cob₂_apply (Φ : H → (ihom (Rep.res π P)).obj A) (g₁ g₂ : H) (x : P) :
    cob₂ π Φ g₁ g₂ x = A.ρ g₁ (ev π (Φ g₂) (P.ρ (π g₁⁻¹) x)) - ev π (Φ (g₁ * g₂)) x + ev π (Φ g₁) x := by
  change ev π (((ihom (Rep.res π P)).obj A).ρ g₁ (Φ g₂) - Φ (g₁ * g₂) + Φ g₁) x = _
  rfl

lemma cob₂_add (Φ Φ' : H → (ihom (Rep.res π P)).obj A) (g₁ g₂ : H) (x : P) :
    cob₂ π (Φ + Φ') g₁ g₂ x = cob₂ π Φ g₁ g₂ x + cob₂ π Φ' g₁ g₂ x := by
  simp only [cob₂, map_add, Pi.add_apply, ev_add]

lemma cob₂_sub (Φ Φ' : H → (ihom (Rep.res π P)).obj A) (g₁ g₂ : H) (x : P) :
    cob₂ π (Φ - Φ') g₁ g₂ x = cob₂ π Φ g₁ g₂ x - cob₂ π Φ' g₁ g₂ x := by
  simp only [cob₂, map_sub, Pi.sub_apply, ev_sub]

include hιeq in

lemma cob₂_apply_f (a : D → (ihom R).obj X) (ha : a ∈ cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψ : ∀ (d : D) (x : R), ev π (ψ d) (f.hom x) = ι (evD (a d) x)) (g₁ g₂ : H) (x : R) :
    cob₂ π (ψ ∘ π) g₁ g₂ (f.hom x) = 0 := by
  simp only [cob₂_apply, Function.comp_apply]
  rw [← Rep.hom_comm_apply f, hψ, hψ, hψ, ← hιeq, ← map_sub ι, ← map_add ι, map_mul, map_inv, cocycle_evD a ha, map_zero]

noncomputable def mOf₂ (Φ : H → (ihom (Rep.res π P)).obj A) (gg : H × H) : M := by
  classical
  exact if hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob₂ π Φ gg.1 gg.2 x then hex.choose else 0

include hfg hg hκ hιeq in
lemma κ_mOf₂ (a : D → (ihom R).obj X) (ha : a ∈ cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψ : ∀ (d : D) (x : R), ev π (ψ d) (f.hom x) = ι (evD (a d) x)) (g₁ g₂ : H) (x : P) :
    κ (g.hom x) (mOf₂ π g κ (ψ ∘ π) (g₁, g₂)) = cob₂ π (ψ ∘ π) g₁ g₂ x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob₂ π (ψ ∘ π) g₁ g₂ x :=
    exists_forall_κ_eq f g κ hfg hg hκ (cob₂ π (ψ ∘ π) g₁ g₂) (cob₂_apply_f π f ι hιeq a ha ψ hψ g₁ g₂)
  simp only [mOf₂, dif_pos hex]
  exact hex.choose_spec x

include hg hκ hκeq in

lemma mem_cocycles₂_of_forall_κ (Φ : H → (ihom (Rep.res π P)).obj A) (m : H × H → M)
    (hm : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m (g₁, g₂)) = cob₂ π Φ g₁ g₂ x) : m ∈ cocycles₂ M := by
  rw [mem_cocycles₂_iff]
  intro g₁ g₂ g₃
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  have hΦ := (mem_cocycles₂_iff _).1 (d₁₂_apply_mem_cocycles₂ (A := (ihom (Rep.res π P)).obj A) Φ) g₁ g₂ g₃
  have hΦx := congrArg (fun t => ev π t x) hΦ
  simp only [ev_add, ev_ρ] at hΦx
  rw [map_add, map_add, hm, hm, hm, κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hm]
  exact hΦx

include hg hκ in

lemma isLevelConstant₂_of_forall_κ (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ (d : D) (x : P), A.ρ s (ev π (ψ d) x) = ev π (ψ d) x)
    (m : H × H → M) (hm : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m (g₁, g₂)) = cob₂ π (ψ ∘ π) g₁ g₂ x) :
    IsLevelConstant₂ r m := by
  obtain ⟨F₁, hF₁, h₁⟩ := hπlev
  obtain ⟨F₂, hF₂, h₂⟩ := hψlev
  haveI := hF₁
  haveI := hF₂
  refine ⟨F₁ ⊔ F₂, inferInstance, fun g₁ g₂ s s' hs hs' => ?_⟩
  have hs₁ : π s = 1 := h₁ s (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
  have hs'₁ : π s' = 1 := h₁ s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs')
  have hs₂ := h₂ s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [hm, hm, cob₂_apply, cob₂_apply]
  simp only [Function.comp_apply, map_mul π, map_inv π, hs₁, hs'₁, mul_one, mul_inv_rev, inv_one, one_mul, map_mul (A.ρ),
    Module.End.mul_apply, hs₂]

include hg hκ hκeq in

lemma sub_eq_d₁₂ (ψ ψ' : D → (ihom (Rep.res π P)).obj A) (m m' : H × H → M)
    (hm : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m (g₁, g₂)) = cob₂ π (ψ ∘ π) g₁ g₂ x)
    (hm' : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m' (g₁, g₂)) = cob₂ π (ψ' ∘ π) g₁ g₂ x)
    (e : D → M) (he : ∀ (d : D) (x : P), κ (g.hom x) (e d) = ev π (ψ d - ψ' d) x) :
    m - m' = (d₁₂ M).hom (e ∘ π) := by
  funext gg
  obtain ⟨g₁, g₂⟩ := gg
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [Pi.sub_apply, map_sub, hm, hm', d₁₂_hom_apply, map_add, map_sub, κ_ρ π κ hκeq, ← Rep.hom_comm_apply g]
  simp only [Function.comp_apply, he, ev_sub, map_mul, cob₂_apply, map_sub]
  abel

lemma isLevelConstant₁_comp_π (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    {Y : Type} (e : D → Y) : IsLevelConstant₁ r (e ∘ π) := by
  obtain ⟨F, hF, h⟩ := hπlev
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, map_mul, h s hs, mul_one]⟩

noncomputable def br (τ : (ihom (Rep.res π P)).obj A) (u : H) : P →+ A := ev π (((ihom (Rep.res π P)).obj A).ρ u τ)

lemma br_apply (τ : (ihom (Rep.res π P)).obj A) (u : H) (y : P) : br π τ u y = A.ρ u (ev π τ (P.ρ (π u⁻¹) y)) := rfl

lemma br_one (τ : (ihom (Rep.res π P)).obj A) (y : P) : br π τ 1 y = ev π τ y := by
  simp only [br_apply, inv_one, map_one, Module.End.one_apply]

lemma ev_ρ_eq_br (τ : (ihom (Rep.res π P)).obj A) (u : H) (y : P) : ev π (((ihom (Rep.res π P)).obj A).ρ u τ) y = br π τ u y := rfl

lemma ρ_ev_eq_br (τ : (ihom (Rep.res π P)).obj A) (u : H) (y : P) : A.ρ u (ev π τ (P.ρ (π u⁻¹) y)) = br π τ u y := rfl

lemma ρ_ev_ρ_sub (τ : (ihom (Rep.res π P)).obj A) (u s : H) (hs : ∀ y : P, A.ρ s (ev π τ y) = ev π τ y)
    (hsu : ∀ y : P, A.ρ (u⁻¹ * s * u) (ev π τ y) = ev π τ y) (x : P) :
    A.ρ s (ev π (((ihom (Rep.res π P)).obj A).ρ u τ - τ) x) = ev π (((ihom (Rep.res π P)).obj A).ρ u τ - τ) x := by
  rw [ev_sub, map_sub, hs, ev_ρ_eq_br, br_apply, ← Module.End.mul_apply, ← map_mul,
    show s * u = u * (u⁻¹ * s * u) by group, map_mul, Module.End.mul_apply, hsu]

lemma ρ_br (τ : (ihom (Rep.res π P)).obj A) (u v : H) (y : P) : A.ρ u (br π τ v (P.ρ (π u⁻¹) y)) = br π τ (u * v) y := by
  simp only [br_apply, mul_inv_rev, map_mul, Module.End.mul_apply]

include hκeq in
lemma κ_g_ρ (u : H) (m : M) (x : P) : κ (g.hom x) (M.ρ u m) = A.ρ u (κ (g.hom (P.ρ (π u⁻¹) x)) m) := by
  rw [κ_ρ π κ hκeq, Rep.hom_comm_apply g]

include hfg hg hκ in
lemma κ_nOf_of_cob_f (ψ : (ihom (Rep.res π P)).obj A) (h : H) (hc : ∀ x : R, cob π ψ h (f.hom x) = 0) (x : P) :
    κ (g.hom x) (nOf π g κ ψ h) = cob π ψ h x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x := exists_forall_κ_eq f g κ hfg hg hκ (cob π ψ h) hc
  simp only [nOf, dif_pos hex]
  exact hex.choose_spec x

include hιeq in

lemma cob_apply_f_of_ker (t : (ihom R).obj X) (τ : (ihom (Rep.res π P)).obj A) (hτ : ∀ x : R, ev π τ (f.hom x) = ι (evD t x))
    (kk : H) (hkk : π kk = 1) (x : R) : cob π τ kk (f.hom x) = 0 := by
  rw [cob_apply, map_inv, hkk, inv_one, ρ_one_apply, hτ, ← hιeq, hkk, ρ_one_apply, sub_self]

include hfg hg hκ hιeq in

lemma κ_ε (t : (ihom R).obj X) (τ : (ihom (Rep.res π P)).obj A) (hτ : ∀ x : R, ev π τ (f.hom x) = ι (evD t x))
    (kk : H) (hkk : π kk = 1) (y : P) : κ (g.hom y) (nOf π g κ τ kk) = br π τ kk y - ev π τ y := by
  rw [κ_nOf_of_cob_f π f g κ hfg hg hκ τ kk (cob_apply_f_of_ker π f ι hιeq t τ hτ kk hkk), cob_apply, br_apply]

include hfg hg hκ hιeq hκeq in

lemma κ_e (t : (ihom R).obj X) (τ : (ihom (Rep.res π P)).obj A) (hτ : ∀ x : R, ev π τ (f.hom x) = ι (evD t x))
    (σ : D → H) (hσ : ∀ h : H, π (σ (π h)) = π h) (u : H) (x : P) :
    κ (g.hom x) (M.ρ u (nOf π g κ τ (u⁻¹ * σ (π u)))) = br π τ (σ (π u)) x - br π τ u x := by
  have hkk : π (u⁻¹ * σ (π u)) = 1 := by rw [map_mul, hσ, map_inv, inv_mul_cancel]
  rw [κ_g_ρ π g κ hκeq, κ_ε π f g ι κ hfg hg hιeq hκ t τ hτ _ hkk, map_sub, ρ_br, mul_inv_cancel_left, ← br_one π τ, ρ_br, mul_one]

include hfg hg hκ hιeq hκeq in

lemma eq_d₁₂_of_σ (t : (ihom R).obj X) (τ : (ihom (Rep.res π P)).obj A) (hτ : ∀ x : R, ev π τ (f.hom x) = ι (evD t x))
    (σ : D → H) (hσ : ∀ h : H, π (σ (π h)) = π h) (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψ : ∀ h : H, ψ (π h) = ((ihom (Rep.res π P)).obj A).ρ (σ (π h)) τ - τ)
    (m : H × H → M) (hm : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m (g₁, g₂)) = cob₂ π (ψ ∘ π) g₁ g₂ x) :
    m = (d₁₂ M).hom (fun u => M.ρ u (nOf π g κ τ (u⁻¹ * σ (π u)))) := by
  funext gg
  obtain ⟨g₁, g₂⟩ := gg
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [hm, d₁₂_hom_apply, map_add, map_sub, κ_g_ρ π g κ hκeq g₁, κ_e π f g ι κ hfg hg hιeq hκeq hκ t τ hτ σ hσ,
    κ_e π f g ι κ hfg hg hιeq hκeq hκ t τ hτ σ hσ, κ_e π f g ι κ hfg hg hιeq hκeq hκ t τ hτ σ hσ, map_sub, ρ_br, ρ_br, cob₂_apply]
  simp only [Function.comp_apply, hψ, ev_sub, map_sub, ev_ρ_eq_br, ρ_ev_eq_br, ρ_br]
  abel

include hg hκ in

lemma isLevelConstant₁_e (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    (τ : (ihom (Rep.res π P)).obj A)
    (hτlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (ev π τ x) = ev π τ x)
    (σ : D → H)
    (hκe : ∀ (u : H) (x : P), κ (g.hom x) (M.ρ u (nOf π g κ τ (u⁻¹ * σ (π u)))) = br π τ (σ (π u)) x - br π τ u x) :
    IsLevelConstant₁ r (fun u => M.ρ u (nOf π g κ τ (u⁻¹ * σ (π u)))) := by
  obtain ⟨F₁, hF₁, h₁⟩ := hπlev
  obtain ⟨F₂, hF₂, h₂⟩ := hτlev
  haveI := hF₁
  haveI := hF₂
  refine ⟨F₁ ⊔ F₂, inferInstance, fun u s hs => ?_⟩
  have hs₁ : π s = 1 := h₁ s (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
  have hs₂ := h₂ s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [hκe, hκe, map_mul, hs₁, mul_one, ← ρ_br, br_apply π τ s, map_inv, hs₁, inv_one, ρ_one_apply, hs₂, ← br_apply]

lemma evD_ext {V W : Rep.{0} k D} {s t : (ihom V).obj W} (hst : ∀ x : V, evD s x = evD t x) : s = t := LinearMap.ext hst

include hκeq in

lemma cob₂_θ (e₀ : H → M) (θ : H → (ihom (Rep.res π P)).obj A) (hθ : ∀ (h : H) (x : P), ev π (θ h) x = κ (g.hom x) (e₀ h))
    (g₁ g₂ : H) (x : P) : cob₂ π θ g₁ g₂ x = κ (g.hom x) ((d₁₂ M).hom e₀ (g₁, g₂)) := by
  rw [cob₂_apply, hθ, hθ, hθ, d₁₂_hom_apply, map_add, map_sub, κ_g_ρ π g κ hκeq]

lemma sub_mem_cocycles₁ (Φ θ : H → (ihom (Rep.res π P)).obj A) (h : ∀ (g₁ g₂ : H) (x : P), cob₂ π Φ g₁ g₂ x = cob₂ π θ g₁ g₂ x) :
    Φ - θ ∈ cocycles₁ ((ihom (Rep.res π P)).obj A) := by
  rw [cocycles₁, LinearMap.mem_ker]
  funext gg
  obtain ⟨g₁, g₂⟩ := gg
  apply ev_ext π
  intro x
  change cob₂ π (Φ - θ) g₁ g₂ x = ev π (0 : (ihom (Rep.res π P)).obj A) x
  rw [cob₂_sub, h, sub_self]
  rfl

omit [CommRing k] in
lemma IsLevelConstant₁.sub' {Y : Type} [AddGroup Y] (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {u v : H → Y}
    (hu : IsLevelConstant₁ r u) (hv : IsLevelConstant₁ r v) : IsLevelConstant₁ r (u - v) := by
  obtain ⟨F₁, hF₁, h₁⟩ := hu
  obtain ⟨F₂, hF₂, h₂⟩ := hv
  haveI := hF₁
  haveI := hF₂
  refine ⟨F₁ ⊔ F₂, inferInstance, fun h s hs => ?_⟩
  rw [Pi.sub_apply, Pi.sub_apply, h₁ h s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h₂ h s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

end hyps

def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

theorem toIntLinearMapOfModules_apply {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) (m : V) : @DFunLike.coe _ _ _ (@LinearMap.instFunLike ℤ ℤ V W _ _ _ _ instV instW (RingHom.id ℤ))
      (toIntLinearMapOfModules instV instW u) m = u m := rfl

def modAdd {U V : ModuleCat.{0} k} (F : U ⟶ V) : U →+ V := F.hom.toAddMonoidHom

lemma modAdd_apply {U V : ModuleCat.{0} k} (F : U ⟶ V) (u : U) : modAdd F u = F.hom u := rfl

section desc

variable (W : Rep.{0} k D) {N : Type} [AddCommGroup N]

def bdry : AddSubgroup (cocycles₁ W) := (LinearMap.range (shortComplexH1 W).moduleCatToCycles).toAddSubgroup

noncomputable def descH1 (F : cocycles₁ W →+ N) (hF : ∀ y : W, F ⟨(d₀₁ W).hom y, d₀₁_apply_mem_cocycles₁ y⟩ = 0) : H1 W →+ N :=
  (QuotientAddGroup.lift (bdry W) F (by
      rintro _ ⟨y, rfl⟩
      exact hF y)).comp (modAdd (H1Iso W).hom)

lemma descH1_H1π (F : cocycles₁ W →+ N) (hF : ∀ y : W, F ⟨(d₀₁ W).hom y, d₀₁_apply_mem_cocycles₁ y⟩ = 0) (c : cocycles₁ W) :
    descH1 W F hF ((H1π W).hom c) = F c := by
  have h2 : H1π W ≫ (H1Iso W).hom = (shortComplexH1 W).moduleCatLeftHomologyData.π := by
    rw [groupCohomology.H1π, Category.assoc, π_comp_H1Iso_hom, Iso.inv_hom_id_assoc]
  have key : modAdd (H1Iso W).hom ((H1π W).hom c) = ((shortComplexH1 W).moduleCatLeftHomologyData.π).hom c :=
    congrArg (fun G => modAdd G c) h2
  have hker : bdry W ≤ F.ker := by
    rintro _ ⟨y, rfl⟩
    exact hF y
  have key' := congrArg (QuotientAddGroup.lift (bdry W) F hker) key
  exact key'.trans rfl

end desc

end LB1EX

open LB1EX in

theorem solution
    {H : Type} [Group H] (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {D : Type} [Group D] (π : H →* D) (hπ : Function.Surjective π)
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B) (hf : Function.Injective f.hom)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {X : Rep ℤ D} {A : Rep ℤ H} (ι : X →+ A) (hι : Function.Injective ι)
    (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
    (hιfix : ∀ a : A, (∀ s : H, π s = 1 → A.ρ s a = a) → ∃ x : X, ι x = a)
    {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R →+ X, ∃ ψ : (ihom (Rep.res π P)).obj A,
      (∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ x)) ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom ψ x) = LinearMap.toAddMonoidHom ψ x)
    (h90 : ∀ u : cocycles₁ ((ihom (Rep.res π P)).obj A), IsLevelConstant₁ r (u : H → (ihom (Rep.res π P)).obj A) →
      ∃ χ : (ihom (Rep.res π P)).obj A,
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x) ∧
        (d₀₁ ((ihom (Rep.res π P)).obj A)).hom χ = (u : H → (ihom (Rep.res π P)).obj A))
    {Λ : H1 ((ihom R).obj X) →+ continuousH2 r M} (hΛ : IsLocalBridge₂ r π f g ι κ Λ) :
    Function.Injective Λ := by
  classical
  have _ := hι
  have _ := hf

  haveI : Finite D := by
    obtain ⟨F₀, hF₀, hπ₀⟩ := hπlev
    haveI := hF₀
    let Φ : H → (F₀ →ₐ[ℚ] AlgebraicClosure ℚ) := fun h => ((r h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
      AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).comp F₀.val
    have hΦ : ∀ h h' : H, Φ h = Φ h' → π h = π h' := by
      intro h h' hh
      have hmem : r (h⁻¹ * h') ∈ F₀.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have := congrArg (fun ψ : F₀ →ₐ[ℚ] AlgebraicClosure ℚ => ψ ⟨x, hx⟩) hh
        simp only [Φ, AlgHom.coe_comp, Function.comp_apply] at this
        change (r h) x = (r h') x at this
        rw [map_mul, map_inv, AlgEquiv.mul_apply, ← this]
        exact (r h).symm_apply_apply x
      have := hπ₀ _ hmem
      rwa [map_mul, map_inv, inv_mul_eq_one] at this
    choose σ hσ using hπ
    refine Finite.of_injective (fun d => Φ (σ d)) (fun d d' hdd => ?_)
    rw [← hσ d, ← hσ d', hΦ _ _ hdd]

  choose Ψ hΨ FΨ hFΨ using hdiv
  have hΨ' : ∀ (φ : R →+ X) (x : R), ev π (Ψ φ) (f.hom x) = ι (φ x) := hΨ
  rw [injective_iff_map_eq_zero]
  intro y hy
  induction y using H1_induction_on with
  | h a =>

  let ψ : D → (ihom (Rep.res π P)).obj A := fun d => Ψ (evD ((a : D → (ihom R).obj X) d))
  have hψ : ∀ (d : D) (x : R), ev π (ψ d) (f.hom x) = ι (evD ((a : D → (ihom R).obj X) d) x) := fun d x => hΨ' _ x
  have hψlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ (d : D) (x : P), A.ρ s (ev π (ψ d) x) = ev π (ψ d) x := by
    haveI : ∀ d : D, FiniteDimensional ℚ (FΨ (evD ((a : D → (ihom R).obj X) d))) := fun d => (hFΨ _).1
    refine ⟨⨆ d, FΨ (evD ((a : D → (ihom R).obj X) d)), inferInstance, fun s hs d x => (hFΨ (evD ((a : D → (ihom R).obj X) d))).2 s ?_ x⟩
    exact IntermediateField.fixingSubgroup_antitone (le_iSup (fun d => FΨ (evD ((a : D → (ihom R).obj X) d))) d) hs
  have hm := κ_mOf₂ π f g ι κ hfg hg hιeq hκ a a.2 ψ hψ
  have hmem : mOf₂ π g κ (ψ ∘ π) ∈ levelCocycles₂ r M :=
    ⟨mem_cocycles₂_of_forall_κ π g κ hg hκeq hκ _ _ hm, isLevelConstant₂_of_forall_κ π g κ hg hκ r hπlev ψ hψlev _ hm⟩

  have h0 : continuousH2π r M ⟨_, hmem⟩ = 0 := (hΛ a ψ hψ hψlev _ hm hmem).symm.trans hy
  obtain ⟨e₀, he₀lev, he₀⟩ := (mem_levelCoboundaries₂_iff r M _).1 ((continuousH2π_eq_zero_iff r M _).1 h0)

  let θ : H → (ihom (Rep.res π P)).obj A := fun h => toIntLinearMapOfModules _ _ ((κ.flip (e₀ h)).comp (homAdd g))
  have hθ : ∀ (h : H) (x : P), ev π (θ h) x = κ (g.hom x) (e₀ h) := fun h x => rfl
  have hu : ψ ∘ π - θ ∈ cocycles₁ ((ihom (Rep.res π P)).obj A) :=
    sub_mem_cocycles₁ π (ψ ∘ π) θ (fun g₁ g₂ x => by
      rw [cob₂_θ π g κ hκeq e₀ θ hθ, he₀, hm])
  have hulev : IsLevelConstant₁ r (ψ ∘ π - θ) :=
    IsLevelConstant₁.sub' r (isLevelConstant₁_comp_π π r hπlev ψ) (he₀lev.comp (fun m : M => (toIntLinearMapOfModules _ _ ((κ.flip m).comp (homAdd g)) : (ihom (Rep.res π P)).obj A)))
  obtain ⟨χ, -, hdχ⟩ := h90 ⟨_, hu⟩ hulev

  have hgf : ∀ x : R, g.hom (f.hom x) = 0 := fun x => (hfg (f.hom x)).2 ⟨x, rfl⟩
  have star : ∀ (h : H) (x : R), ι (evD ((a : D → (ihom R).obj X) (π h)) x) =
      A.ρ h (ev π χ (f.hom (R.ρ (π h)⁻¹ x))) - ev π χ (f.hom x) := by
    intro h x
    have h1 := congrFun hdχ h
    have h2 := congrArg (fun tt => ev π tt (f.hom x)) h1
    simp only at h2
    change cob π χ h (f.hom x) = ev π (ψ (π h) - θ h) (f.hom x) at h2
    rw [ev_sub, hψ, hθ, hgf, map_zero, AddMonoidHom.zero_apply, sub_zero, cob_apply, ← Rep.hom_comm_apply f, map_inv] at h2
    exact h2.symm

  have hfix : ∀ (x : R) (s : H), π s = 1 → A.ρ s (ev π χ (f.hom x)) = ev π χ (f.hom x) := by
    intro x s hs
    have := star s x
    rw [hs, inv_one, ρ_one_apply, show (a : D → (ihom R).obj X) 1 = 0 from cocycles₁_map_one a, evD_zero, map_zero] at this
    exact (sub_eq_zero.1 this.symm)
  choose tf htf using fun x : R => hιfix (ev π χ (f.hom x)) (hfix x)
  have tf_add : ∀ x y, tf (x + y) = tf x + tf y := fun x y => hι (by
    rw [map_add, htf, htf, htf, ← homAdd_apply f, ← homAdd_apply f, ← homAdd_apply f, map_add (homAdd f), map_add (ev π χ)])
  let t : (ihom R).obj X := toIntLinearMapOfModules _ _ (AddMonoidHom.mk' tf tf_add)
  have ht : ∀ x : R, evD t x = tf x := fun x => rfl

  refine (H1π_eq_zero_iff a).2 ⟨t, funext fun d => ?_⟩
  obtain ⟨h, rfl⟩ := hπ d
  apply evD_ext
  intro x
  apply hι
  rw [d₀₁_hom_apply, evD_sub, evD_ρ, map_sub, hιeq, ht, ht, htf, htf, star]

end S_groupCohomology_isLocalBridge2_injective
end P2MW
export P2MW.S_groupCohomology_isLocalBridge2_injective (solution)
