-- Prove2me | solution 1 for groupCohomology.exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/dbff9fa2-3d9c-5e59-89c7-a6dc8b0d8462

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer

set_option autoImplicit false

theorem solution
    {G : Type} [Group G] [Finite G] {X : Type} [MulAction G X]
    (ν : G → G → X →₀ ℤ)
    (hν : ∀ g h k : G, Finsupp.mapDomain (g • ·) (ν h k) - ν (g * h) k + ν g (h * k) - ν g h = 0)
    (hloc : ∀ x₀ : X, ∃ β : ↥(MulAction.stabilizer G x₀) → ℤ,
      ∀ s t : ↥(MulAction.stabilizer G x₀), ν s t x₀ = β s + β t - β (s * t)) :
    ∃ μ : G → X →₀ ℤ, ∀ g h : G, ν g h = Finsupp.mapDomain (g • ·) (μ h) - μ (g * h) + μ g := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  have hmd : ∀ (g : G) (φ : X →₀ ℤ) (x : X), Finsupp.mapDomain (g • ·) φ x = φ (g⁻¹ • x) := fun g φ x => by
    conv_lhs => rw [← smul_inv_smul g x]
    exact Finsupp.mapDomain_apply (MulAction.injective g) φ (g⁻¹ • x)

  have hcoc : ∀ (g h j : G) (x : X),
      ν h j (g⁻¹ • x) - ν (g * h) j x + ν g (h * j) x - ν g h x = 0 := by
    intro g h j x
    have e := DFunLike.congr_fun (hν g h j) x
    simp only [Finsupp.sub_apply, Finsupp.add_apply, hmd, Finsupp.coe_zero, Pi.zero_apply] at e
    linarith

  have hst' : ∀ x₀ : X, ∃ β : G → ℤ, ∀ s t : G, s • x₀ = x₀ → t • x₀ = x₀ →
      ν s t x₀ = β s + β t - β (s * t) := by
    intro x₀
    obtain ⟨β, hβ⟩ := hloc x₀
    refine ⟨fun g => if hg : g ∈ MulAction.stabilizer G x₀ then β ⟨g, hg⟩ else 0, fun s t hs ht => ?_⟩
    have hs' : s ∈ MulAction.stabilizer G x₀ := MulAction.mem_stabilizer_iff.mpr hs
    have ht' : t ∈ MulAction.stabilizer G x₀ := MulAction.mem_stabilizer_iff.mpr ht
    have hst'' : s * t ∈ MulAction.stabilizer G x₀ := mul_mem hs' ht'
    simp only [dif_pos hs', dif_pos ht', dif_pos hst'']
    exact hβ ⟨s, hs'⟩ ⟨t, ht'⟩
  choose β hβ using hst'

  let rep : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hrep : ∀ x, ∃ t : G, t • rep x = x := fun x => by
    have : rep x ∈ MulAction.orbit G x := Quotient.mk_out (s := MulAction.orbitRel G X) x
    obtain ⟨g, hg⟩ := this
    exact ⟨g⁻¹, by rw [← hg]; simp⟩
  have hrep_smul : ∀ (g : G) (x : X), rep (g • x) = rep x := fun g x => by
    show (Quotient.mk (MulAction.orbitRel G X) (g • x)).out = (Quotient.mk (MulAction.orbitRel G X) x).out
    congr 1
    exact Quotient.sound ⟨g, rfl⟩
  choose t ht using hrep
  have htinv : ∀ x, (t x)⁻¹ • x = rep x := fun x => by rw [inv_smul_eq_iff, ht x]

  have hu : ∀ (g : G) (x : X), ((t x)⁻¹ * g * t (g⁻¹ • x)) • rep x = rep x := by
    intro g x
    calc ((t x)⁻¹ * g * t (g⁻¹ • x)) • rep x
        = (t x)⁻¹ • g • t (g⁻¹ • x) • rep (g⁻¹ • x) := by rw [hrep_smul, mul_smul, mul_smul]
      _ = rep x := by rw [ht, smul_inv_smul, htinv]

  let Y : Finset X := Finset.univ.biUnion fun p : G × G × G =>
    (ν p.2.1 p.2.2).support.image fun x => p.1 • x
  have hY : ∀ x, x ∉ Y → ∀ (k a c : G), ν a c (k • x) = 0 := by
    intro x hx k a c
    by_contra h
    exact hx (Finset.mem_biUnion.mpr ⟨(k⁻¹, a, c), Finset.mem_univ _,
      Finset.mem_image.mpr ⟨k • x, Finsupp.mem_support_iff.mpr h, inv_smul_smul k x⟩⟩)
  have hYsmul : ∀ (g : G) (x : X), x ∉ Y → g • x ∉ Y := by
    intro g x hx hgx
    obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp hgx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hp
    have hz' : z = (p.1⁻¹ * g) • x := by rw [mul_smul, ← hzx, inv_smul_smul]
    exact (Finsupp.mem_support_iff.mp hz) (hz' ▸ hY x hx (p.1⁻¹ * g) p.2.1 p.2.2)

  let M : G → X → ℤ := fun g x => if x ∈ Y then
      ν g (t (g⁻¹ • x)) x - ν (t x) ((t x)⁻¹ * g * t (g⁻¹ • x)) x
        + β (rep x) ((t x)⁻¹ * g * t (g⁻¹ • x)) else 0
  have hMsupp : ∀ (g : G) (x : X), M g x ≠ 0 → x ∈ Y := fun g x h => by
    by_contra hx
    exact h (if_neg hx)
  let μ : G → X →₀ ℤ := fun g => Finsupp.onFinset Y (M g) (hMsupp g)
  have hμ : ∀ (g : G) (x : X), μ g x = M g x := fun g x => rfl
  refine ⟨μ, fun g h => Finsupp.ext fun x => ?_⟩
  rw [Finsupp.add_apply, Finsupp.sub_apply, hmd, hμ, hμ, hμ]
  by_cases hx : x ∈ Y
  · have hy : g⁻¹ • x ∈ Y := by
      by_contra hy
      exact hYsmul g _ hy (by rwa [smul_inv_smul])
    simp only [M, if_pos hx, if_pos hy]
    have hz' : (g * h)⁻¹ • x = h⁻¹ • g⁻¹ • x := by rw [mul_inv_rev, mul_smul]
    rw [hz', hrep_smul]

    set y : X := g⁻¹ • x with hy_def
    set z : X := h⁻¹ • y with hz_def
    set u : G := (t x)⁻¹ * g * t y with hu_def
    set w : G := (t y)⁻¹ * h * t z with hw_def
    have huw : (t x)⁻¹ * (g * h) * t z = u * w := by
      simp only [hu_def, hw_def]; group
    rw [huw]
    have e1 : g * t y = t x * u := by simp only [hu_def]; group
    have e2 : h * t z = t y * w := by simp only [hw_def]; group
    have hux : u • rep x = rep x := hu g x
    have hwx : w • rep x = rep x := by
      have := hu h y
      rwa [hrep_smul] at this
    have hA := hcoc g h (t z) x
    have hB := hcoc g (t y) w x
    have hC := hcoc (t x) u w x
    rw [e1, ← e2, ← hy_def] at hB
    rw [← hy_def] at hA
    rw [htinv, hβ (rep x) u w hux hwx] at hC
    linarith
  · have hy : g⁻¹ • x ∉ Y := hYsmul _ _ hx
    simp only [M, if_neg hx, if_neg hy]
    have h0 := hY x hx 1 g h
    rw [one_smul] at h0
    rw [h0]; ring

end S_groupCohomology_exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer
end P2MW
export P2MW.S_groupCohomology_exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer (solution)
