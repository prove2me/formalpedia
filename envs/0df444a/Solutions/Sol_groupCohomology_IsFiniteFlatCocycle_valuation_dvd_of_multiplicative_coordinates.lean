-- Prove2me | solution 1 for groupCohomology.IsFiniteFlatCocycle.valuation_dvd_of_multiplicative_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:09:09.431646+00:00
-- url     : https://prove2.me/submissions/52475750-0968-4d57-b7f2-81764da4bbb2

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
import Theorems.Thm_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation

set_option autoImplicit false

namespace groupCohomology

/-- Finite-flat multiplicative Kummer cocycles have valuation divisible by the
residue prime. The multiplicative coordinates explicitly identify the coefficient
line with roots of unity and the cocycle with the motion of the chosen radical. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (c : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W)
    (hc : IsFiniteFlatCocycle p ρ c)
    (μ : W → PadicAlgCl p) (hμinj : Function.Injective μ)
    (hμzero : μ 0 = 1) (hμadd : ∀ v w, μ (v + w) = μ v * μ w)
    (hμroot : ∀ w, μ w ^ p = 1)
    (hμact : ∀ σ w, μ (ρ σ w) = σ (μ w))
    (x : ℚ_[p]) (γ : PadicAlgCl p)
    (hγ : γ ^ p = algebraMap ℚ_[p] (PadicAlgCl p) x)
    (hKummer : ∀ σ, μ (c σ) * γ = σ γ) :
    (p : ℤ) ∣ Padic.valuation x := by
  classical
  rcases hc with ⟨H, hH, hHopf, hfin, hflat, hcomm, e, he, hact⟩
  letI := hH
  letI := hHopf
  letI := hfin
  letI := hflat
  letI := hcomm
  have hezero : e 1 = 0 := by
    apply add_left_cancel (a := e 1)
    simpa using (he 1 1).symm
  have hepow (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) (n : ℕ) :
      e (f ^ n) = n • e f := by
    induction n with
    | zero => simp [hezero]
    | succ n ih => rw [pow_succ, he, ih, succ_nsmul]
  have hμnsmul (w : W) (n : ℕ) : μ (n • w) = μ w ^ n := by
    induction n with
    | zero => simp [hμzero]
    | succ n ih => rw [succ_nsmul, hμadd, ih, pow_succ]
  have hHp : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), f ^ p = 1 := by
    intro f
    apply e.injective
    rw [hepow, hezero, ← Nat.cast_smul_eq_nsmul (ZMod p)]
    simp
  let D : Submonoid (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) :=
    { carrier := {f | (e f).2 = 0}
      one_mem' := by simp [hezero]
      mul_mem' := by
        intro f g hf hg
        change (e f).2 = 0 at hf
        change (e g).2 = 0 at hg
        change (e (f * g)).2 = 0
        rw [he]
        change (e f).2 + (e g).2 = 0
        rw [hf, hg, add_zero] }
  have hDcyc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ n : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ n) →
      ∀ f ∈ D, ∀ g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        (∀ h : H, g h = σ (f h)) → g = f ^ n := by
    intro σ _ n hn f hf g hfg
    have hfzero : (e f).2 = 0 := hf
    apply e.injective
    rw [hact σ f g hfg, hepow]
    apply Prod.ext
    · change ρ σ (e f).1 + (e f).2 • c σ = n • (e f).1
      rw [hfzero, zero_smul, add_zero]
      apply hμinj
      rw [hμact, hn _ (hμroot _), hμnsmul]
    · change (e f).2 = n • (e f).2
      simp [hfzero]
  have hquot : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        (∀ h : H, g h = σ (f h)) → ∃ d ∈ D, g = f * d := by
    intro σ _ f g hfg
    let d := e.symm (e g - e f)
    have hed : e d = e g - e f := e.apply_symm_apply _
    refine ⟨d, ?_, ?_⟩
    · change (e d).2 = 0
      rw [hed, hact σ f g hfg]
      change (e f).2 - (e f).2 = 0
      exact sub_self _
    · apply e.injective
      rw [he, hed]
      abel
  obtain ⟨t, u, β, hu, huI, hβ, hfix⟩ :=
    HopfAlgebra.exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
      p hp2 H hHp D hDcyc hquot
  by_cases hx : (p : ℤ) ∣ Padic.valuation x
  · exact hx
  · obtain ⟨σ, hσ, hζ, hroots, hmove⟩ :=
      PadicAlgCl.exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation
        p u β hu huI hβ x hx γ hγ
    let f := e.symm (0, 1)
    let g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) :=
      WithConv.toConv ((σ.restrictScalars ℤ_[p]).toAlgHom.comp f.ofConv)
    have hfg : ∀ h : H, g h = σ (f h) := fun _ => rfl
    have hgf : g = f := hfix σ hσ hζ hroots f g hfg
    have hcoords := hact σ f g hfg
    rw [hgf] at hcoords
    have hczero : c σ = 0 := by
      have h := congrArg Prod.fst hcoords
      simpa [f] using h.symm
    have hγfix : σ γ = γ := by
      rw [← hKummer σ, hczero, hμzero, one_mul]
    exact False.elim (hmove hγfix)

end groupCohomology
