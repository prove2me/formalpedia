-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_scale_split_bound
-- name    : AvramDividend.Classical.p2m81_scale_split_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T09:34:18.919889+00:00
-- url     : https://prove2.me/theorems/da7cbea3-0d23-4f27-9300-7f07e1a27688
-- title:
--   Scale Laplace split upper bound for Tauberian contradiction
-- statement:
--   Given scale-like hypotheses (nonnegativity, monotonicity on [0,oo), Laplace identity 1/(psi-q) on (0,oo), base point beta0 with value K, and eventual positivity of the exponent), the ratio beta/(psi(beta)-q) is eventually at most W a + beta*exp(-(beta-beta0)*a)*K. Helper D3 for parent fc6b315a: splits (0,oo)=(0,a] u (a,oo) via integral_union_ae, applies head bound D1 and tail bound D2, multiplies by beta and rewrites with the Laplace equation. Monotonicity is the unfolded forall-form matching IsScaleFunction usage.
-- source:
--   Decomposition child D3 of fc6b315a. Proof uses children D1 and D2; statement mirrors IsScaleFunction Laplace field exactly with psi abstracted.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_scale_split_bound (W : ℝ → ℝ) (ψ : ℝ → ℝ) (q a β0 K : ℝ) (ha : 0 < a)
    (hNonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hMono : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ y → W x ≤ W y)
    (hLap : ∀ θ : ℝ, 0 ≤ θ → q < ψ θ → IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * W y) (Ioi (0:ℝ)) ∧
      (∫ y in Ioi (0:ℝ), Real.exp (-(θ * y)) * W y) = (ψ θ - q)⁻¹)
    (hβ0nn : 0 ≤ β0) (hβ0lt : q < ψ β0)
    (hK : (∫ x in Ioi (0:ℝ), Real.exp (-(β0 * x)) * W x) = K)
    (hEv : ∀ᶠ θ in atTop, 0 < θ ∧ q < ψ θ) :
    ∀ᶠ β in atTop, β / (ψ β - q) ≤ W a + β * Real.exp (-(β - β0) * a) * K := by sorry
