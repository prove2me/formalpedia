-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mem_Ioc_pos_of_norm_sub_exp_lt
-- name    : FiniteEnergyPlane.exists_mem_Ioc_pos_of_norm_sub_exp_lt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T13:00:57.287696+00:00
-- url     : https://prove2.me/theorems/e35f91c2-a54d-46d0-bd10-a99cb008263d
-- title:
--   A planar path close to a path turning by three half-turns crosses the positive real axis
-- statement:
--   Let $a \le b$, let $g : [a, b] \to \mathbb{C}$ and $\psi : [a, b] \to \mathbb{R}$ be continuous, with $|g(\sigma) - e^{i\psi(\sigma)}| < 1$ for all $\sigma \in [a, b]$ and $\psi(b) \ge \psi(a) + 3\pi$. Then there is $\sigma \in (a, b]$ with $g(\sigma)$ a positive real number.
--
--   Role: an elementary crossing criterion. It detects when a nonvanishing planar path, close to a path of known total turning, passes through a given ray.
--
--   Formalization Note: continuity is required only on $[a, b]$ (`ContinuousOn`). "Positive real" is expressed as $0 < \mathrm{Re}\, g(\sigma)$ and $\mathrm{Im}\, g(\sigma) = 0$.
-- source:
--   Elementary; used in the proof of U. Hryniewicz, Trans. AMS 364 (2012), Lemma 6.9

import Mathlib

namespace FiniteEnergyPlane

open scoped Real

/-- A continuous path that stays within distance `1` of `e^{iψ}`, where `ψ` increases by at
least `3π`, passes through the positive real axis after its initial time. -/
theorem exists_mem_Ioc_pos_of_norm_sub_exp_lt (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℂ) (ψ : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc a b)) (hψ : ContinuousOn ψ (Set.Icc a b))
    (hclose : ∀ σ ∈ Set.Icc a b, ‖g σ - Complex.exp ((ψ σ : ℂ) * Complex.I)‖ < 1)
    (hinc : ψ a + 3 * π ≤ ψ b) :
    ∃ σ ∈ Set.Ioc a b, 0 < (g σ).re ∧ (g σ).im = 0 := by
  sorry

end FiniteEnergyPlane
