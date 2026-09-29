-- Prove2me | solution 1 for groupCohomology.finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e45f1382-7dc3-5e04-a55d-2869cd335494

import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup
import Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_forall_kummerCocycle_eq_one
import Theorems.Thm_groupCohomology_Kummer_kummerCocycle_conj
import Theorems.Thm_groupCohomology_Kummer_kummerCocycle_pow_eq_one_of_mem_fixingSubgroup
import Theorems.Thm_groupCohomology_Kummer_kummerCocycle_mul_of_mem_fixingSubgroup
import Theorems.Thm_groupCohomology_Kummer_kummerCocycle_mul_eq_of_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist

set_option autoImplicit false
open Module CategoryTheory groupCohomology
open groupCohomology.Kummer

set_option maxHeartbeats 3200000 in
theorem solution
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    (hKG : ∀ (g : Ω ≃ₐ[k] Ω) (x : Ω), x ∈ K → g x ∈ K)
    {p : ℕ} [Fact p.Prime] (χ : (Ω ≃ₐ[k] Ω) →* (ZMod p)ˣ) {ζ : Ωˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : Ω ≃ₐ[k] Ω, g • ζ = ζ ^ (χ g : ZMod p).val) (hζK : (ζ : Ω) ∈ K)
    (hroots : ∀ a : Ω, a ∈ K → a ≠ 0 → ∃ α : Ω, α ^ p = a)
    (A : Rep.{0} (ZMod p) (Ω ≃ₐ[k] Ω)) [FiniteDimensional (ZMod p) A]
    (htriv : ∀ s ∈ K.fixingSubgroup, ∀ v : A, A.ρ s v = v)
    (W : Submodule (ZMod p) (cocycles₁ (Rep.res K.fixingSubgroup.subtype A)))
    (hW : ∀ c, c ∈ W ↔
      (∃ E : IntermediateField k Ω, FiniteDimensional k E ∧
        ∀ (g s : K.fixingSubgroup), (s : Ω ≃ₐ[k] Ω) ∈ E.fixingSubgroup → c (g * s) = c g) ∧
      ∀ (g : Ω ≃ₐ[k] Ω) (s t : K.fixingSubgroup), (g⁻¹ * s * g : Ω ≃ₐ[k] Ω) = t → A.ρ g (c t) = c s)
    {VX : Type} [AddCommGroup VX] [Module (ZMod p) VX] (X : Representation (ZMod p) (Ω ≃ₐ[k] Ω) VX)
    (π : (↥K)ˣ → VX) (hπmul : ∀ a b, π (a * b) = π a + π b) (hπsurj : Function.Surjective π)
    (hπker : ∀ a : (↥K)ˣ, π a = 0 ↔ ∃ b : (↥K)ˣ, b ^ p = a)
    (hπG : ∀ (g : Ω ≃ₐ[k] Ω) (a b : (↥K)ˣ), g ((a : K) : Ω) = ((b : K) : Ω) → X g (π a) = π b) :
    finrank (ZMod p) W = finrank (ZMod p) ((A.dualTwist χ).ρ.linHom X).invariants := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt

  have hζ1 : ζ ^ p = 1 := hζp.pow_eq_one
  have hpowmod : ∀ n : ℕ, ζ ^ (n % p) = ζ ^ n := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hζ1, one_pow, mul_one]
  have pow_val_add : ∀ a b : ZMod p, ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := fun a b => by
    rw [ZMod.val_add, hpowmod, pow_add]
  have pow_val_mul : ∀ a b : ZMod p, (ζ ^ a.val) ^ b.val = ζ ^ (b * a).val := fun a b => by
    rw [← pow_mul, ZMod.val_mul, hpowmod, mul_comm]
  have pow_val_inj : ∀ a b : ZMod p, ζ ^ a.val = ζ ^ b.val → a = b := fun a b h =>
    ZMod.val_injective p (hζp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  have pow_val_eq_one : ∀ a : ZMod p, ζ ^ a.val = 1 → a = 0 := fun a h =>
    pow_val_inj a 0 (by rw [h, ZMod.val_zero, pow_zero])
  have exists_pow_val : ∀ η : Ωˣ, η ^ p = 1 → ∃ m : ZMod p, ζ ^ m.val = η := fun η hη => by
    have hζp' : IsPrimitiveRoot (ζ : Ω) p := IsPrimitiveRoot.coe_units_iff.2 hζp
    obtain ⟨i, hi, hiη⟩ := hζp'.eq_pow_of_pow_eq_one (ξ := (η : Ω))
      (by rw [← Units.val_pow_eq_pow_val, hη, Units.val_one])
    refine ⟨(i : ZMod p), Units.ext ?_⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Units.val_pow_eq_pow_val, hiη]
  have smul_pow_val : ∀ (g : Ω ≃ₐ[k] Ω) (m : ZMod p),
      g • ζ ^ m.val = ζ ^ ((m * (χ g : ZMod p))).val := fun g m => by
    rw [smul_pow', hζ, pow_val_mul]

  have hμ : ∀ η : Ω, η ^ p = 1 → η ∈ K := fun η hη => by
    have hη0 : η ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne p)] at hη
      exact zero_ne_one hη
    obtain ⟨m, hm⟩ := exists_pow_val (Units.mk0 η hη0) (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hη, Units.val_one]))
    have : η = ((ζ ^ m.val : Ωˣ) : Ω) := by rw [hm, Units.val_mk0]
    rw [this, Units.val_pow_eq_pow_val]
    exact pow_mem hζK _

  have hadd : ∀ (c : cocycles₁ (Rep.res K.fixingSubgroup.subtype A)) (s t : K.fixingSubgroup),
      c (s * t) = c s + c t := fun c s t => by
    rw [(mem_cocycles₁_iff (⇑c)).1 c.2 s t]
    change A.ρ (s : Ω ≃ₐ[k] Ω) (c t) + c s = _
    rw [htriv _ s.2, add_comm]
  have hone : ∀ (c : cocycles₁ (Rep.res K.fixingSubgroup.subtype A)), c 1 = 0 := fun c =>
    cocycles₁_map_one c

  let ψ : cocycles₁ (Rep.res K.fixingSubgroup.subtype A) → Module.Dual (ZMod p) A →
      (K.fixingSubgroup →* Ωˣ) := fun c l =>
    { toFun := fun s => ζ ^ (l (c s)).val
      map_one' := by rw [hone c, map_zero, ZMod.val_zero, pow_zero]
      map_mul' := fun s t => by rw [hadd, map_add, pow_val_add] }
  have hψ : ∀ c l (s : K.fixingSubgroup), ψ c l s = ζ ^ (l (c s)).val := fun _ _ _ => rfl
  have hψp : ∀ c l (s : K.fixingSubgroup), ψ c l s ^ p = 1 := fun c l s => by
    rw [hψ, ← pow_mul, mul_comm, pow_mul, hζ1, one_pow]

  have hKP_exists : ∀ c ∈ W, ∀ l, ∃ (a : (↥K)ˣ) (α : Ωˣ), algebraMap K Ω (a : K) = (α : Ω) ^ p ∧
      ∀ s : K.fixingSubgroup, ψ c l s = kummerCocycle α (s : Ω ≃ₐ[k] Ω) := by
    intro c hc l
    obtain ⟨⟨E, hE, hlev⟩, -⟩ := (hW c).1 hc
    exact exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup K hμ (ψ c l) (hψp c l)
      ⟨E, hE, fun τ hτ => by
        rw [hψ, show c τ = 0 by rw [← one_mul τ, hlev 1 τ hτ, hone], map_zero, ZMod.val_zero,
          pow_zero]⟩
  have hκdiv : ∀ (α α' : Ωˣ) (σ : Ω ≃ₐ[k] Ω),
      kummerCocycle (α / α') σ = kummerCocycle α σ / kummerCocycle α' σ := fun α α' σ => by
    rw [eq_div_iff_mul_eq', ← kummerCocycle_mul, div_mul_cancel]
  have hπone : π 1 = 0 := by
    have h := hπmul 1 1
    rw [mul_one] at h
    have h2 : π 1 + π 1 = π 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hKP_unique : ∀ (a a' : (↥K)ˣ) (α α' : Ωˣ), algebraMap K Ω (a : K) = (α : Ω) ^ p →
      algebraMap K Ω (a' : K) = (α' : Ω) ^ p →
      (∀ s : K.fixingSubgroup, kummerCocycle α (s : Ω ≃ₐ[k] Ω) = kummerCocycle α' (s : Ω ≃ₐ[k] Ω)) →
      π a = π a' := by
    intro a a' α α' hα hα' heq
    have hdiv : algebraMap K Ω ((a / a' : (↥K)ˣ) : K) = ((α / α' : Ωˣ) : Ω) ^ p := by
      rw [Units.val_div_eq_div_val, map_div₀, hα, hα', Units.val_div_eq_div_val, div_pow]
    obtain ⟨b, hb⟩ := (exists_pow_eq_iff_forall_kummerCocycle_eq_one K hμ hdiv).2
      (fun s => by rw [hκdiv, heq s, div_self'])
    have h0 : π (a / a') = 0 := (hπker _).2 ⟨b, hb⟩
    have := hπmul (a / a') a'
    rwa [div_mul_cancel, h0, zero_add] at this

  let Ev : W → Module.Dual (ZMod p) A → VX := fun w l => π (hKP_exists w.1 w.2 l).choose
  have hEv : ∀ (w : W) (l : Module.Dual (ZMod p) A) (a : (↥K)ˣ) (α : Ωˣ),
      algebraMap K Ω (a : K) = (α : Ω) ^ p →
      (∀ s : K.fixingSubgroup, ψ w.1 l s = kummerCocycle α (s : Ω ≃ₐ[k] Ω)) → Ev w l = π a := by
    intro w l a α hα hψα
    obtain ⟨α₀, hα₀, hψ₀⟩ := (hKP_exists w.1 w.2 l).choose_spec
    exact hKP_unique _ _ α₀ α hα₀ hα (fun s => by rw [← hψ₀, hψα])
  have hEv_add : ∀ (w : W) (l₁ l₂ : Module.Dual (ZMod p) A), Ev w (l₁ + l₂) = Ev w l₁ + Ev w l₂ := by
    intro w l₁ l₂
    obtain ⟨a₁, α₁, h₁, e₁⟩ := hKP_exists w.1 w.2 l₁
    obtain ⟨a₂, α₂, h₂, e₂⟩ := hKP_exists w.1 w.2 l₂
    rw [hEv w l₁ a₁ α₁ h₁ e₁, hEv w l₂ a₂ α₂ h₂ e₂, ← hπmul]
    refine hEv w (l₁ + l₂) (a₁ * a₂) (α₁ * α₂) (mul_pow_eq h₁ h₂) fun s => ?_
    rw [hψ, LinearMap.add_apply, pow_val_add, ← hψ, ← hψ, e₁, e₂, kummerCocycle_mul]

  let Φ : W → (Module.Dual (ZMod p) A →ₗ[ZMod p] VX) := fun w =>
    (AddMonoidHom.mk' (Ev w) (hEv_add w)).toZModLinearMap p
  have hΦ : ∀ w l, Φ w l = Ev w l := fun _ _ => rfl

  have hconj : ∀ (g : Ω ≃ₐ[k] Ω) (s : Ω ≃ₐ[k] Ω), s ∈ K.fixingSubgroup → g⁻¹ * s * g ∈ K.fixingSubgroup := by
    intro g s hs
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _ (hKG g x hx),
      ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hπeq_imp : ∀ (a a' : (↥K)ˣ) (α α' : Ωˣ), algebraMap K Ω (a : K) = (α : Ω) ^ p →
      algebraMap K Ω (a' : K) = (α' : Ω) ^ p → π a = π a' →
      ∀ s : K.fixingSubgroup, kummerCocycle α (s : Ω ≃ₐ[k] Ω) = kummerCocycle α' (s : Ω ≃ₐ[k] Ω) := by
    intro a a' α α' hα hα' hπ s
    have hdiv : algebraMap K Ω ((a / a' : (↥K)ˣ) : K) = ((α / α' : Ωˣ) : Ω) ^ p := by
      rw [Units.val_div_eq_div_val, map_div₀, hα, hα', Units.val_div_eq_div_val, div_pow]
    have h0 : π (a / a') = 0 := by
      have := hπmul (a / a') a'
      rw [div_mul_cancel, hπ] at this
      have h2 : π a' + 0 = π a' + π (a / a') := by rw [add_zero, add_comm]; exact this
      exact (add_left_cancel h2).symm
    have h1 := (exists_pow_eq_iff_forall_kummerCocycle_eq_one K hμ hdiv).1 ((hπker _).1 h0) s
    rwa [hκdiv, div_eq_one] at h1

  have hgroot : ∀ (g : Ω ≃ₐ[k] Ω) (a : (↥K)ˣ) (α : Ωˣ), algebraMap K Ω (a : K) = (α : Ω) ^ p →
      ∃ b : (↥K)ˣ, g ((a : K) : Ω) = ((b : K) : Ω) ∧ algebraMap K Ω (b : K) = ((g • α : Ωˣ) : Ω) ^ p := by
    intro g a α hα
    have hmem : g ((a : K) : Ω) ∈ K := hKG g _ (a : K).2
    have hne : (⟨g ((a : K) : Ω), hmem⟩ : K) ≠ 0 := by
      intro h
      have : g ((a : K) : Ω) = 0 := congrArg Subtype.val h
      rw [map_eq_zero_iff g g.injective] at this
      exact a.ne_zero (Subtype.ext this)
    refine ⟨Units.mk0 _ hne, rfl, ?_⟩
    change g ((a : K) : Ω) = _
    rw [show ((a : K) : Ω) = algebraMap K Ω (a : K) from rfl, hα, map_pow]
    rfl

  have hinv : ∀ w : W, Φ w ∈ ((A.dualTwist χ).ρ.linHom X).invariants := by
    intro w
    rw [Representation.mem_invariants]
    intro g
    rw [Representation.linHom_apply]
    apply LinearMap.ext
    intro l
    set l' := (A.dualTwist χ).ρ g⁻¹ l with hl'
    have hl : l = (A.dualTwist χ).ρ g l' := by
      rw [hl', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hl']
    conv_rhs => rw [hl]
    obtain ⟨a, α, hα, hψα⟩ := hKP_exists w.1 w.2 l'
    obtain ⟨b, hgb, hb⟩ := hgroot g a α hα
    rw [hΦ, hΦ, hEv w l' a α hα hψα, hπG g a b hgb]
    symm
    refine hEv w _ b (g • α) hb fun s => ?_
    obtain ⟨-, hcj⟩ := (hW w.1).1 w.2
    have ht := hcj g s ⟨_, hconj g s s.2⟩ rfl
    have e1 : ((A.dualTwist χ).ρ g l') ((w : cocycles₁ (Rep.res K.fixingSubgroup.subtype A)) s)
        = l' ((w : cocycles₁ (Rep.res K.fixingSubgroup.subtype A)) ⟨_, hconj g s s.2⟩) * (χ g : ZMod p) := by
      rw [Rep.dualTwist_ρ_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, ← ht,
        ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, mul_comm]
    rw [hψ, e1, ← smul_pow_val, ← hψ, hψα, ← kummerCocycle_conj]
    congr 1
    group

  have hEv_addw : ∀ (w₁ w₂ : W) (l : Module.Dual (ZMod p) A), Ev (w₁ + w₂) l = Ev w₁ l + Ev w₂ l := by
    intro w₁ w₂ l
    obtain ⟨a₁, α₁, h₁, e₁⟩ := hKP_exists w₁.1 w₁.2 l
    obtain ⟨a₂, α₂, h₂, e₂⟩ := hKP_exists w₂.1 w₂.2 l
    rw [hEv w₁ l a₁ α₁ h₁ e₁, hEv w₂ l a₂ α₂ h₂ e₂, ← hπmul]
    refine hEv (w₁ + w₂) l (a₁ * a₂) (α₁ * α₂) (mul_pow_eq h₁ h₂) fun s => ?_
    rw [hψ, show ((w₁ + w₂ : W) : cocycles₁ (Rep.res K.fixingSubgroup.subtype A)) s
        = (w₁ : cocycles₁ (Rep.res K.fixingSubgroup.subtype A)) s
          + (w₂ : cocycles₁ (Rep.res K.fixingSubgroup.subtype A)) s from rfl,
      map_add, pow_val_add, ← hψ, ← hψ, e₁, e₂, kummerCocycle_mul]
  let T : W →ₗ[ZMod p] ((A.dualTwist χ).ρ.linHom X).invariants :=
    (AddMonoidHom.mk' (fun w => (⟨Φ w, hinv w⟩ : ((A.dualTwist χ).ρ.linHom X).invariants))
      (fun w₁ w₂ => Subtype.ext (LinearMap.ext fun l => by
        change Ev (w₁ + w₂) l = Ev w₁ l + Ev w₂ l
        exact hEv_addw w₁ w₂ l))).toZModLinearMap p
  have hT : ∀ (w : W) (l : Module.Dual (ZMod p) A),
      ((T w : ((A.dualTwist χ).ρ.linHom X).invariants) : Module.Dual (ZMod p) A →ₗ[ZMod p] VX) l = Ev w l :=
    fun _ _ => rfl

  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply Subtype.ext
    apply Subtype.ext
    funext s
    show (w : cocycles₁ (Rep.res K.fixingSubgroup.subtype A)) s = 0
    rw [← Module.forall_dual_apply_eq_zero_iff (ZMod p)]
    intro l
    obtain ⟨a, α, hα, hψα⟩ := hKP_exists w.1 w.2 l
    have h0 : Ev w l = 0 := by
      rw [← hT, hw]
      rfl
    rw [hEv w l a α hα hψα] at h0
    have h1 := (exists_pow_eq_iff_forall_kummerCocycle_eq_one K hμ hα).1 ((hπker a).1 h0) s
    rw [← hψα, hψ] at h1
    exact pow_val_eq_one _ h1

  have hπpow : ∀ (x : (↥K)ˣ) (e : ℕ), π (x ^ e) = e • π x := fun x e => by
    induction e with
    | zero => rw [pow_zero, hπone, zero_smul]
    | succ e ih => rw [pow_succ, hπmul, ih, succ_nsmul]
  have hκone : ∀ σ : Ω ≃ₐ[k] Ω, kummerCocycle (1 : Ωˣ) σ = 1 := fun σ => by
    rw [kummerCocycle_apply, smul_one, div_one]
  have hκpow : ∀ (β : Ωˣ) (e : ℕ) (σ : Ω ≃ₐ[k] Ω), kummerCocycle (β ^ e) σ = kummerCocycle β σ ^ e := by
    intro β e σ
    induction e with
    | zero => rw [pow_zero, pow_zero, hκone]
    | succ e ih => rw [pow_succ, kummerCocycle_mul, ih, pow_succ]
  have hpowpair : ∀ (x : (↥K)ˣ) (β : Ωˣ) (e : ℕ), algebraMap K Ω (x : K) = (β : Ω) ^ p →
      algebraMap K Ω ((x ^ e : (↥K)ˣ) : K) = ((β ^ e : Ωˣ) : Ω) ^ p := by
    intro x β e hx
    rw [Units.val_pow_eq_pow_val, map_pow, hx, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, mul_comm]
  have hζsum : ∀ (t : Finset (Fin (finrank (ZMod p) A))) (f : Fin (finrank (ZMod p) A) → ZMod p),
      ζ ^ (∑ i ∈ t, f i).val = ∏ i ∈ t, ζ ^ (f i).val := by
    intro t f
    induction t using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, ZMod.val_zero, pow_zero]
    | insert i t hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, pow_val_add, ih]
  have hnsmul : ∀ (mm : ZMod p) (v : VX), mm.val • v = mm • v := fun mm v => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

  have hTsurj : Function.Surjective T := by
    rintro ⟨F, hF⟩
    let bA := Module.finBasis (ZMod p) A
    have ha : ∀ i : Fin (finrank (ZMod p) A), ∃ (a : (↥K)ˣ) (α : Ωˣ), π a = F (bA.coord i) ∧
        algebraMap K Ω (a : K) = (α : Ω) ^ p := by
      intro i
      obtain ⟨a, hπa⟩ := hπsurj (F (bA.coord i))
      obtain ⟨α, hαp⟩ := hroots ((a : K) : Ω) (a : K).2 (fun h => a.ne_zero (Subtype.ext h))
      have hα0 : α ≠ 0 := by
        rintro rfl
        rw [zero_pow (NeZero.ne p)] at hαp
        exact a.ne_zero (Subtype.ext hαp.symm)
      exact ⟨a, Units.mk0 α hα0, hπa, by rw [Units.val_mk0, hαp]; rfl⟩
    choose a α hπa hα using ha
    have hdl : ∀ (i : Fin (finrank (ZMod p) A)) (s : K.fixingSubgroup), ∃ mm : ZMod p,
        ζ ^ mm.val = kummerCocycle (α i) (s : Ω ≃ₐ[k] Ω) := fun i s =>
      exists_pow_val _ (kummerCocycle_pow_eq_one_of_mem_fixingSubgroup K (hα i) s.2)
    choose m hm using hdl
    have hm_mul : ∀ i (s t : K.fixingSubgroup), m i (s * t) = m i s + m i t := by
      intro i s t
      apply pow_val_inj
      rw [hm, pow_val_add, hm, hm, Subgroup.coe_mul]
      exact kummerCocycle_mul_of_mem_fixingSubgroup K hμ (hα i) s.2 t.2
    let cf : K.fixingSubgroup → A := fun s => ∑ i, m i s • bA i
    have hcf_mem : cf ∈ cocycles₁ (Rep.res K.fixingSubgroup.subtype A) := by
      rw [mem_cocycles₁_iff]
      intro s t
      change cf (s * t) = A.ρ (s : Ω ≃ₐ[k] Ω) (cf t) + cf s
      rw [htriv _ s.2]
      simp only [cf, hm_mul, add_smul, Finset.sum_add_distrib, add_comm]
    let c : cocycles₁ (Rep.res K.fixingSubgroup.subtype A) := ⟨cf, hcf_mem⟩
    have hc : ∀ s, c s = ∑ i, m i s • bA i := fun _ => rfl

    have hprodpair : ∀ e : Fin (finrank (ZMod p) A) → ℕ,
        algebraMap K Ω ((∏ i, a i ^ e i : (↥K)ˣ) : K) = ((∏ i, α i ^ e i : Ωˣ) : Ω) ^ p ∧
        π (∏ i, a i ^ e i) = ∑ i, e i • π (a i) ∧
        ∀ σ : Ω ≃ₐ[k] Ω, kummerCocycle (∏ i, α i ^ e i) σ = ∏ i, kummerCocycle (α i) σ ^ e i := by
      intro e
      refine Finset.induction_on (Finset.univ : Finset (Fin (finrank (ZMod p) A))) ?_ ?_
      · refine ⟨?_, ?_, fun σ => ?_⟩
        · rw [Finset.prod_empty, Finset.prod_empty, Units.val_one, map_one, Units.val_one, one_pow]
        · rw [Finset.prod_empty, Finset.sum_empty, hπone]
        · rw [Finset.prod_empty, Finset.prod_empty, hκone]
      · intro i t hi ih
        obtain ⟨ih1, ih2, ih3⟩ := ih
        refine ⟨?_, ?_, fun σ => ?_⟩
        · rw [Finset.prod_insert hi, Finset.prod_insert hi]
          exact mul_pow_eq (hpowpair _ _ _ (hα i)) ih1
        · rw [Finset.prod_insert hi, Finset.sum_insert hi, hπmul, hπpow, ih2]
        · rw [Finset.prod_insert hi, Finset.prod_insert hi, kummerCocycle_mul, hκpow, ih3]
    have hstar : ∀ l : Module.Dual (ZMod p) A, ∃ (al : (↥K)ˣ) (αl : Ωˣ),
        algebraMap K Ω (al : K) = (αl : Ω) ^ p ∧ π al = F l ∧
        ∀ s : K.fixingSubgroup, ζ ^ (l (c s)).val = kummerCocycle αl (s : Ω ≃ₐ[k] Ω) := by
      intro l
      obtain ⟨h1, h2, h3⟩ := hprodpair (fun i => (l (bA i)).val)
      refine ⟨_, _, h1, ?_, fun s => ?_⟩
      · rw [h2]
        conv_rhs => rw [← bA.sum_dual_apply_smul_coord l, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hnsmul, map_smul, hπa]
      · rw [h3, hc, map_sum, hζsum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul, ← hm i s, pow_val_mul, mul_comm]

    have hint : ∀ i, IsIntegral k ((α i : Ωˣ) : Ω) := fun i => by
      refine IsIntegral.of_pow (NeZero.pos p) ?_
      rw [← hα i]
      exact (Algebra.IsIntegral.isIntegral (R := k) ((a i : (↥K)ˣ) : K)).algebraMap
    let E : IntermediateField k Ω := IntermediateField.adjoin k (Set.range fun i => ((α i : Ωˣ) : Ω))
    haveI hEfd : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨i, rfl⟩; exact hint i)
    have hlev : ∀ (g s : K.fixingSubgroup), (s : Ω ≃ₐ[k] Ω) ∈ E.fixingSubgroup → c (g * s) = c g := by
      intro g s hs
      rw [hc, hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      apply pow_val_inj
      rw [hm, hm, Subgroup.coe_mul]
      exact kummerCocycle_mul_eq_of_apply_eq (α i) _ _
        ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _
          (IntermediateField.subset_adjoin k _ ⟨i, rfl⟩))
    have hFinv : ∀ (g : Ω ≃ₐ[k] Ω) (l : Module.Dual (ZMod p) A),
        X g (F (l ∘ₗ A.ρ g)) = (χ g : ZMod p) • F l := by
      intro g l
      have h := hF g
      rw [Representation.linHom_apply] at h
      have h' := LinearMap.congr_fun h ((A.dualTwist χ).ρ g (l ∘ₗ A.ρ g))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply] at h'
      rw [h', Rep.dualTwist_ρ_apply, map_smul, LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul,
        mul_inv_cancel, map_one, Module.End.one_eq_id, LinearMap.comp_id]
    have hcj : ∀ (g : Ω ≃ₐ[k] Ω) (s t : K.fixingSubgroup), (g⁻¹ * s * g : Ω ≃ₐ[k] Ω) = t →
        A.ρ g (c t) = c s := by
      intro g s t hst
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (ZMod p)]
      intro l
      rw [map_sub, sub_eq_zero, ← LinearMap.comp_apply]
      obtain ⟨a₁, α₁, hα₁, hπ₁, hζ₁⟩ := hstar (l ∘ₗ A.ρ g)
      obtain ⟨a₀, α₀, hα₀, hπ₀, hζ₀⟩ := hstar l
      obtain ⟨b₁, hgb₁, hb₁⟩ := hgroot g a₁ α₁ hα₁
      have hπb : π b₁ = π (a₀ ^ (χ g : ZMod p).val) := by
        rw [← hπG g a₁ b₁ hgb₁, hπ₁, hFinv, hπpow, hnsmul, hπ₀]
      have hκeq := hπeq_imp b₁ (a₀ ^ (χ g : ZMod p).val) (g • α₁) (α₀ ^ (χ g : ZMod p).val) hb₁
        (hpowpair _ _ _ hα₀) hπb s
      have e2 : kummerCocycle α₁ (t : Ω ≃ₐ[k] Ω) = g⁻¹ • kummerCocycle (g • α₁) (s : Ω ≃ₐ[k] Ω) := by
        have hconjκ := kummerCocycle_conj α₁ g (t : Ω ≃ₐ[k] Ω)
        rw [← hst, show g * (g⁻¹ * (s : Ω ≃ₐ[k] Ω) * g) * g⁻¹ = s by group] at hconjκ
        rw [hconjκ, inv_smul_smul, ← hst]
      apply pow_val_inj
      rw [hζ₁ t, e2, hκeq, hκpow, ← hζ₀ s, pow_val_mul, smul_pow_val, mul_comm ((χ g : ZMod p)) _,
        mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, mul_one]
    refine ⟨⟨c, (hW c).2 ⟨⟨E, hEfd, hlev⟩, hcj⟩⟩, Subtype.ext (LinearMap.ext fun l => ?_)⟩
    rw [hT]
    obtain ⟨al, αl, hαl, hπl, hζl⟩ := hstar l
    rw [hEv _ l al αl hαl (fun s => by rw [hψ]; exact hζl s), hπl]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩)

end S_groupCohomology_finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
end P2MW
export P2MW.S_groupCohomology_finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist (solution)
