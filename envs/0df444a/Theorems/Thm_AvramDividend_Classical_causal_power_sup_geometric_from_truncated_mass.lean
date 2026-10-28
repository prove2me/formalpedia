-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_power_sup_geometric_from_truncated_mass
-- name    : AvramDividend.Classical.causal_power_sup_geometric_from_truncated_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:06:38.58579+00:00
-- url     : https://prove2.me/theorems/2cb8024b-07f4-425f-86a9-b165509956f3
-- title:
--   Uniform sup-norm geometric decay from causal convolution-power mass bounds
-- statement:
--   If a causal kernel κ is globally bounded above by B≥0, and its nonnegative causal convolution powers have mass at most ρ^(n+1) on every initial interval, then every successor power has the pointwise uniform bound F(n+1)(x)≤Bρ^(n+1) for x≥0. This converts existing proved L1 geometric mass estimates into the L-infinity geometric bounds needed for the Weierstrass M-test and continuity of the positive-discount Neumann scale series.
-- source:
--   Pointwise bounded integrand plus Mathlib integral_mono_ae and Bochner integral_const_mul; apply causal_positive_convolution_powers_geometric_truncated_mass.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_power_sup_geometric_from_truncated_mass
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (B ρ : ℝ)
    (hB : 0 ≤ B) (hκle : ∀ t : ℝ, κ t ≤ B)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFstep : ∀ n : ℕ, ∀ x : ℝ, F (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume)
    (hFprod : ∀ n : ℕ, ∀ x : ℝ,
      IntegrableOn (fun s : ℝ => κ (x - s) * F n s)
        (Ioc (0 : ℝ) x) volume)
    (hFi : ∀ n : ℕ, ∀ x : ℝ,
      IntegrableOn (F n) (Ioc (0 : ℝ) x) volume)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      F (n + 1) x ≤ B * ρ ^ (n + 1) := by sorry
