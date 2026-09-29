-- Prove2me | solution 1 for fta_winding_power_loop_no_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-03T21:44:50.972743+00:00
-- url     : https://prove2.me/submissions/408efe55-c951-4e0c-822b-523fd880fbd9

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Definitions.Def_fta_winding_infra

noncomputable section
open Complex Polynomial
open scoped Real

/-- A continuous `ℝ → ℝ` whose values all lie in the discrete set `2π·ℤ` is constant:
between two distinct values an intermediate value (off the lattice) would be attained by
the IVT on the connected line. -/
private theorem const_of_mem_twopi_zmultiples (g : ℝ → ℝ) (hg : Continuous g)
    (hmem : ∀ s : ℝ, ∃ m : ℤ, g s = m * (2 * Real.pi)) :
    ∀ a b : ℝ, g a = g b := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have step : ∀ a b : ℝ, g a < g b → False := by
    intro a b hlt
    obtain ⟨ma, hma⟩ := hmem a
    obtain ⟨mb, hmb⟩ := hmem b
    have hgap : g a + 2 * Real.pi ≤ g b := by
      have hzpos : (0 : ℝ) < ((mb - ma : ℤ) : ℝ) := by
        have : g b - g a = ((mb - ma : ℤ) : ℝ) * (2 * Real.pi) := by
          push_cast; rw [hma, hmb]; ring
        nlinarith [this, hlt, hpi]
      have hz1 : (1 : ℤ) ≤ mb - ma := by exact_mod_cast hzpos
      have : ((mb - ma : ℤ) : ℝ) * (2 * Real.pi) = g b - g a := by
        push_cast; rw [hma, hmb]; ring
      have h1 : (1 : ℝ) * (2 * Real.pi) ≤ ((mb - ma : ℤ) : ℝ) * (2 * Real.pi) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hz1
      linarith [this, h1]
    set v := g a + Real.pi with hv
    have hvmem : v ∈ Set.Icc (g a) (g b) := by
      constructor <;> [linarith; linarith]
    have hconn : IsPreconnected (g '' Set.univ) :=
      (isPreconnected_univ.image g hg.continuousOn)
    have hsub : Set.Icc (g a) (g b) ⊆ g '' Set.univ :=
      hconn.Icc_subset ⟨a, trivial, rfl⟩ ⟨b, trivial, rfl⟩
    obtain ⟨t, -, ht⟩ := hsub hvmem
    obtain ⟨mt, hmt⟩ := hmem t
    have : ((mt - ma : ℤ) : ℝ) * (2 * Real.pi) = Real.pi := by
      have e1 : g t = v := ht
      rw [hmt] at e1
      push_cast; rw [hma] at *; nlinarith [e1, hma]
    have hcast : ((2 * (mt - ma) : ℤ) : ℝ) = (1 : ℤ) := by
      have : ((mt - ma : ℤ) : ℝ) * 2 = 1 := by
        have hpne : Real.pi ≠ 0 := ne_of_gt hpi
        field_simp at this ⊢
        nlinarith [this]
      push_cast; push_cast at this; linarith
    have : (2 * (mt - ma) : ℤ) = 1 := by exact_mod_cast hcast
    omega
  intro a b
  rcases lt_trichotomy (g a) (g b) with h | h | h
  · exact (step a b h).elim
  · exact h
  · exact (step b a h).elim

theorem solution (u : Circle) (n : ℕ) (hn : 0 < n) :
    ¬ FtaHasLift (FtaLeadingLoop u n) := by
  rintro ⟨Γ, hΓcont, hΓ⟩
  set G : ℝ → ℝ := fun s => Γ ((s : FtaCircle)) with hG
  have hGcont : Continuous G := hΓcont.comp (continuous_coinduced_rng)
  -- the lift equation, pulled back to ℝ (no surjectivity of exp needed)
  have key : ∀ s : ℝ, Circle.exp (G s) = u * Circle.exp (n * s) := by
    intro s
    have := hΓ ((s : FtaCircle))
    simp only [FtaLeadingLoop, AddCircle.homeomorphCircle'_apply_mk] at this
    rw [hG, this, ← Circle.exp_natCast_mul]
  have key2 : ∀ s : ℝ, Circle.exp (G s - n * s) = u := by
    intro s; rw [Circle.exp_sub, key s]; simp
  set φ : ℝ → ℝ := fun s => G s - n * s - G 0 with hφ
  have hφcont : Continuous φ := by
    apply (hGcont.sub _).sub continuous_const
    exact (continuous_const.mul continuous_id)
  have hφmem : ∀ s : ℝ, ∃ m : ℤ, φ s = m * (2 * Real.pi) := by
    intro s
    have heq : Circle.exp (G s - n * s) = Circle.exp (G 0 - n * 0) := by rw [key2 s, key2 0]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
    refine ⟨m, ?_⟩
    rw [hφ]; simp only
    simp only [mul_zero, sub_zero] at hm
    linarith [hm]
  have hconst := const_of_mem_twopi_zmultiples φ hφcont hφmem 0 (2 * Real.pi)
  have hper : G (2 * Real.pi) = G 0 := by
    rw [hG]; simp only
    congr 1
    show ((2 * Real.pi : ℝ) : FtaCircle) = ((0 : ℝ) : FtaCircle)
    rw [AddCircle.coe_period]; simp
  rw [hφ] at hconst
  simp only at hconst
  rw [hper] at hconst
  have hn0 : (n : ℝ) * (2 * Real.pi) = 0 := by
    simp only [mul_zero, sub_zero] at hconst; linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have : (n : ℝ) = 0 := by
    rcases mul_eq_zero.mp hn0 with h | h
    · exact h
    · exfalso; linarith
  have : n = 0 := by exact_mod_cast this
  omega
