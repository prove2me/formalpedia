-- Prove2me | Theorems.Thm_BranchNearRepair_uniform_window_and_core
-- name    : BranchNearRepair.uniform_window_and_core
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T16:14:40.505865+00:00
-- url     : https://prove2.me/theorems/8bb9e914-5cf8-4982-973b-191d90a66750
-- title:
--   Uniform positivity on bounded scaled windows and a fixed inner margin
-- statement:
--   Let kₙ≥1 be integers, let hₙ>0 tend to zero, and fix A≥1. Put xₙ=kₙ/hₙ². For real ε and γ define
--   \[
--   P_n(\varepsilon,\gamma)=\Re\left(\frac{x_n}{x_n+\gamma^2-\varepsilon^2-2i\varepsilon\gamma}\right)^{k_n}.
--   \]
--   For all sufficiently large n, uniformly over |ε|≤1/2 and 0≤γ with γhₙ≤A, one has Pₙ(ε,γ)>0. On the inner window γhₙ≤1, the stronger lower bound Pₙ(ε,γ)≥e⁻¹/2 holds. The threshold can depend on A but not on ε or γ. This analytic statement requires no assumption that ε=0 and asserts no conclusion about RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Two-cutoff repair for the small-scale escape argument, 2026-11-16. Complete elementary Lean proof; no claim of mathematical novelty.

import Mathlib

theorem BranchNearRepair.uniform_window_and_core (k : ℕ → ℕ) (hk : ∀ n, 1≤k n)
    (h : ℕ → ℝ) (hh : ∀ n, 0<h n) (ht : Filter.Tendsto h Filter.atTop (nhds 0))
    (A : ℝ) (hA : 1≤A) :
    ∀ᶠ n in Filter.atTop, ∀ e g : ℝ, |e|≤1/2 → 0≤g → g*h n≤A →
    0 < (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/
      (((k n : ℝ)/(h n)^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^(k n)).re ∧
    (g*h n≤1 → Real.exp (-1)/2 ≤ (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/
      (((k n : ℝ)/(h n)^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^(k n)).re) := by sorry
