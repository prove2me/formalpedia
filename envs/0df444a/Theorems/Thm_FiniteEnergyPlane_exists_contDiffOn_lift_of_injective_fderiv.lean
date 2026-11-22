-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_lift_of_injective_fderiv
-- name    : FiniteEnergyPlane.exists_contDiffOn_lift_of_injective_fderiv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:27:11.754425+00:00
-- url     : https://prove2.me/theorems/e9eb075c-e904-4629-926e-62b1d703e425
-- title:
--   Lifting a C^n curve through a map with injective derivative
-- statement:
--   Let $E,F$ be finite-dimensional real normed spaces of the same dimension, $n\ge1$, $O\subseteq E$ open and $f:E\to F$ of class $C^n$ on $O$. Let $a\in O$ with $Df(a)$ injective, and let $g:\mathbb{R}\to F$ be of class $C^n$ on $(t_0-\delta,t_0+\delta)$, $\delta>0$, with $g(t_0)=f(a)$. Then there are $\varepsilon>0$ and a curve $c:\mathbb{R}\to E$ of class $C^n$ on $(t_0-\varepsilon,t_0+\varepsilon)$ with $c(t_0)=a$ such that $c(t)\in O$ and $f(c(t))=g(t)$ for every $t\in(t_0-\varepsilon,t_0+\varepsilon)$.
--
--   It is used to solve equations of the form $f(c(t))=g(t)$ with regular dependence on the parameter $t$.
--
--   **Formalization Note** "Same dimension" is `Module.finrank ℝ E = Module.finrank ℝ F`; the intervals are `Metric.ball t₀ δ` and `Metric.ball t₀ ε`.
-- source:
--   Standard calculus fact (local inverses of maps with invertible derivative)

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Lifting a curve through a map with injective derivative between spaces of equal finite
dimension. Let `f : E → F` be `C^n` (`n ≥ 1`) on an open set `O`, `a ∈ O` with `Df(a)` injective,
and `g : ℝ → F` a `C^n` curve on `(t₀ - δ, t₀ + δ)` with `g t₀ = f a`. Then for some `ε > 0` there
is a `C^n` curve `c` on `(t₀ - ε, t₀ + ε)` with `c t₀ = a`, `c t ∈ O` and `f (c t) = g t`. -/
theorem exists_contDiffOn_lift_of_injective_fderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ E = Module.finrank ℝ F) {n : ℕ}
    (hn : 1 ≤ n) {O : Set E} (hO : IsOpen O) {f : E → F} (hf : ContDiffOn ℝ n f O) {a : E}
    (ha : a ∈ O) (hinj : Function.Injective (fderiv ℝ f a)) {g : ℝ → F} {t₀ δ : ℝ} (hδ : 0 < δ)
    (hg : ContDiffOn ℝ n g (ball t₀ δ)) (hga : g t₀ = f a) :
    ∃ ε > 0, ∃ c : ℝ → E, ContDiffOn ℝ n c (ball t₀ ε) ∧ c t₀ = a ∧
      ∀ t ∈ ball t₀ ε, c t ∈ O ∧ f (c t) = g t := by
  sorry

end FiniteEnergyPlane
