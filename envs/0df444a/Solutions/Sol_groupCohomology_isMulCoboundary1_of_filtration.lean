-- Prove2me | solution 1 for groupCohomology.isMulCoboundary1_of_filtration
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9151983e-1b27-5f20-b4cb-c7ebcd2357c3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_isMulCoboundary1_of_filtration

set_option autoImplicit false
open groupCohomology

set_option maxHeartbeats 1600000 in
theorem solution
    {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (F : ℕ → Subgroup M) (hF0 : F 0 = ⊤)
    (hstab : ∀ (n : ℕ) (g : G) (x : M), x ∈ F n → g • x ∈ F n)
    (hcomplete : ∀ s : ℕ → M, (∀ n, s (n + 1) / s n ∈ F n) → ∃ x : M, ∀ n, x / s n ∈ F n)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 1)
    (hgr : ∀ (n : ℕ) (f : G → M), (∀ g, f g ∈ F n) → IsMulCocycle₁ f →
      ∃ a ∈ F n, ∀ g, f g / (g • a / a) ∈ F (n + 1))
    (f : G → M) (hf : IsMulCocycle₁ f) : IsMulCoboundary₁ f := by

  have step : ∀ (n : ℕ) (b : M), (∀ g, f g / (g • b / b) ∈ F n) →
      ∃ a ∈ F n, ∀ g, f g / (g • (b * a) / (b * a)) ∈ F (n + 1) := by
    intro n b hb
    have hcoc : IsMulCocycle₁ (fun g => f g / (g • b / b)) := by
      intro g h
      simp only [hf g h, mul_smul, smul_div']
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel
    obtain ⟨a, haF, ha⟩ := hgr n _ hb hcoc
    refine ⟨a, haF, fun g => ?_⟩
    have e : f g / (g • (b * a) / (b * a)) = f g / (g • b / b) / (g • a / a) := by
      simp only [smul_mul']
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel
    rw [e]
    exact ha g
  choose! step hstepF hstepP using step

  obtain ⟨b, hb0, hbs⟩ : ∃ b : ℕ → M, b 0 = 1 ∧ ∀ n, b (n + 1) = b n * step n (b n) :=
    ⟨fun n => Nat.rec 1 (fun k bk => bk * step k bk) n, rfl, fun n => rfl⟩
  have hbP : ∀ n g, f g / (g • b n / b n) ∈ F n := by
    intro n
    induction n with
    | zero => intro g; rw [hF0]; exact Subgroup.mem_top _
    | succ n ih => intro g; rw [hbs]; exact hstepP n (b n) ih g
  have hbC : ∀ n, b (n + 1) / b n ∈ F n := by
    intro n
    have e : b (n + 1) / b n = step n (b n) := by
      rw [hbs]
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel
    rw [e]
    exact hstepF n (b n) (hbP n)
  obtain ⟨x, hx⟩ := hcomplete b hbC
  refine ⟨x, fun g => ?_⟩
  have hmem : ∀ n, f g / (g • x / x) ∈ F n := by
    intro n
    have e : f g / (g • x / x) = f g / (g • b n / b n) / (g • (x / b n) / (x / b n)) := by
      simp only [smul_div']
      apply Additive.ofMul.injective; simp only [ofMul_div]; abel
    rw [e]
    exact (F n).div_mem (hbP n g) ((F n).div_mem (hstab n g _ (hx n)) (hx n))
  have h1 := hsep _ hmem
  rw [div_eq_one] at h1
  exact h1.symm

end S_groupCohomology_isMulCoboundary1_of_filtration
end P2MW
export P2MW.S_groupCohomology_isMulCoboundary1_of_filtration (solution)
