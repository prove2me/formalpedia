-- Prove2me | solution 1 for groupCohomology.finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/46d3e80c-e7da-578d-bae5-3c711790dfd9

import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import Theorems.Thm_LinearMap_finrank_ker_dualMap_eq_finrank_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u

theorem solution
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (χ : G →* kˣ) (N : Subgroup G) (hχN : ∀ n ∈ N, χ n = 1)
    (φ : G) (hgen : ∀ g, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ N) (a : k) (hχφ : (χ φ : k) = a)

    (D : Type u) [AddCommGroup D] [Module k D] [FiniteDimensional k D]
    (π : M →ₗ[k] D) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π = ⨆ n ∈ N, LinearMap.range (M.ρ n - 1))
    (φD : D →ₗ[k] D) (hφD : φD ∘ₗ π = π ∘ₗ M.ρ φ) :
    finrank k (M.dualTwist χ).ρ.invariants = finrank k (LinearMap.ker (φD - a • 1)) := by
  classical

  have hπN : ∀ n ∈ N, ∀ x, π (M.ρ n x) = π x := by
    intro n hn x
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, hker]
    refine Submodule.mem_iSup_of_mem n (Submodule.mem_iSup_of_mem hn ⟨x, ?_⟩)
    rw [LinearMap.sub_apply, Module.End.one_apply]
  have hφDπ : ∀ y, φD (π y) = π (M.ρ φ y) := fun y => LinearMap.congr_fun hφD y

  let K : Submodule k (Module.Dual k D) := LinearMap.ker (φD - a • 1).dualMap
  have hK : ∀ fb : Module.Dual k D, fb ∈ K ↔ ∀ y, fb (φD y) = a * fb y := by
    intro fb
    rw [LinearMap.mem_ker]
    constructor
    · intro h y
      have := LinearMap.congr_fun h y
      rw [LinearMap.dualMap_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, map_smul, smul_eq_mul, LinearMap.zero_apply, sub_eq_zero] at this
      exact this
    · intro h
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.dualMap_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, map_smul, smul_eq_mul, LinearMap.zero_apply, sub_eq_zero]
      exact h y

  have hinv : ∀ v, M.ρ φ (M.ρ φ⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hmem : ∀ fb ∈ K, (fb ∘ₗ π) ∈ (M.dualTwist χ).ρ.invariants := by
    intro fb hfb
    rw [hK] at hfb

    let St : Subgroup G :=
      { carrier := {g | (M.dualTwist χ).ρ g (fb ∘ₗ π) = fb ∘ₗ π}
        mul_mem' := fun {x y} hx hy => by
          change (M.dualTwist χ).ρ (x * y) (fb ∘ₗ π) = fb ∘ₗ π
          rw [map_mul, Module.End.mul_apply, hy, hx]
        one_mem' := by
          change (M.dualTwist χ).ρ 1 (fb ∘ₗ π) = fb ∘ₗ π
          rw [map_one, Module.End.one_apply]
        inv_mem' := fun {x} hx => by
          change (M.dualTwist χ).ρ x⁻¹ (fb ∘ₗ π) = fb ∘ₗ π
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hNst : N ≤ St := by
      intro n hn
      change (M.dualTwist χ).ρ n (fb ∘ₗ π) = fb ∘ₗ π
      refine LinearMap.ext fun x => ?_
      rw [Rep.dualTwist_ρ_apply, hχN n hn, Units.val_one, one_smul, LinearMap.comp_apply,
        LinearMap.comp_apply, LinearMap.comp_apply, hπN n⁻¹ (inv_mem hn) x]
    have hφst : φ ∈ St := by
      change (M.dualTwist χ).ρ φ (fb ∘ₗ π) = fb ∘ₗ π
      refine LinearMap.ext fun x => ?_
      rw [Rep.dualTwist_ρ_apply, hχφ, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.comp_apply, LinearMap.comp_apply, smul_eq_mul, ← hfb, hφDπ, hinv]
    intro g
    obtain ⟨n, hn⟩ := hgen g
    have hg : g = φ ^ n * ((φ ^ n)⁻¹ * g) := by group
    have : g ∈ St := by
      rw [hg]
      exact St.mul_mem (St.pow_mem hφst n) (hNst hn)
    exact this
  let Λ : K →ₗ[k] (M.dualTwist χ).ρ.invariants :=
    { toFun := fun fb => ⟨fb.1 ∘ₗ π, hmem fb.1 fb.2⟩
      map_add' := fun x y => by ext v; rfl
      map_smul' := fun c x => by ext v; rfl }
  have hΛinj : Function.Injective Λ := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    change x.1 ∘ₗ π = y.1 ∘ₗ π at h
    exact LinearMap.cancel_right hπ |>.1 h
  have hΛsurj : Function.Surjective Λ := by
    rintro ⟨f, hf⟩

    have hfN : ∀ n ∈ N, ∀ x, f (M.ρ n x) = f x := by
      intro n hn x
      have h' := LinearMap.congr_fun (hf n⁻¹) x
      rw [Rep.dualTwist_ρ_apply, hχN n⁻¹ (inv_mem hn), Units.val_one, one_smul, inv_inv,
        LinearMap.comp_apply] at h'
      exact h'
    have hle : LinearMap.ker π ≤ LinearMap.ker f := by
      rw [hker]
      refine iSup₂_le fun n hn => ?_
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_sub, hfN n hn x,
        sub_self]
    let e := π.quotKerEquivOfSurjective hπ
    let fb : Module.Dual k D := (LinearMap.ker π).liftQ f hle ∘ₗ e.symm.toLinearMap
    have hfbπ : ∀ x, fb (π x) = f x := by
      intro x
      change (LinearMap.ker π).liftQ f hle (e.symm (π x)) = f x
      have : e.symm (π x) = Submodule.Quotient.mk x := by
        rw [LinearEquiv.symm_apply_eq]
        rfl
      rw [this, Submodule.liftQ_apply]
    have hfbK : fb ∈ K := by
      rw [hK]
      intro y
      obtain ⟨x, rfl⟩ := hπ y
      rw [hφDπ, hfbπ, hfbπ]
      have h := LinearMap.congr_fun (hf φ) (M.ρ φ x)
      rw [Rep.dualTwist_ρ_apply, hχφ, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul,
        ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
      exact h.symm
    refine ⟨⟨fb, hfbK⟩, Subtype.ext (LinearMap.ext fun x => ?_)⟩
    exact hfbπ x
  have hfin := (LinearEquiv.ofBijective Λ ⟨hΛinj, hΛsurj⟩).finrank_eq
  rw [← hfin]
  exact LinearMap.finrank_ker_dualMap_eq_finrank_ker _

end S_groupCohomology_finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul
end P2MW
export P2MW.S_groupCohomology_finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul (solution)
