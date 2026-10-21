-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_hjb_discounted_finite_dividend_bound
-- name    : AvramDividend.Classical.local_verification_hjb_discounted_finite_dividend_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T14:51:23.027924+00:00
-- url     : https://prove2.me/theorems/978744c4-2289-4b43-be74-a1ddb7cfe6e8
-- title:
--   A finite sequence of capped HJB dividend payments has discounted total at most the initial candidate value
-- statement:
--   Fix q≥0 and a verification function satisfying the HJB gradient/smoothness conditions on [0,C]. A sequence of reserve states u_k and admissible dividend payments d_k with u_(k+1)=u_k−d_k, 0≤d_k≤u_k and ofReal(u_k)≤C has a nonnegative terminal candidate value w(u_n)≥0. For arbitrary nonnegative payment times τ_k, the discounted total ∑_{k<n} e^(−qτ_k)d_k does not exceed w(u_0). Each discount is at most one since q,τ≥0, so the discounted sum is bounded by the undiscounted sum, which the already Proved finite-payment HJB telescoping theorem bounds by w(u_0)−w(u_n)≤w(u_0). The theorem accounts for a possible initial atom at τ=0 and models the deterministic finite-payment part of the stochastic budget; it deliberately assumes reserves change only by the specified dividend payments, not by Lévy increments. It does not claim the general controlled stochastic result.
-- source:
--   Depends on Proved local_verification_hjb_finite_dividend_telescoping target a7b8173d-98a3-4a01-a7db-ed2b67ae33b3 and standard exponential/finite sum inequalities; no Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_finite_dividend_telescoping

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_hjb_discounted_finite_dividend_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (u d : ℕ → ℝ) (times : ℕ → ℝ≥0)
    (hupdate : ∀ k : ℕ, u (k + 1) = u k - d k)
    (hpos : ∀ k : ℕ, 0 ≤ d k)
    (hsolv : ∀ k : ℕ, d k ≤ u k)
    (hcap : ∀ k : ℕ, ENNReal.ofReal (u k) ≤ C)
    (n : ℕ) (hterminal : 0 ≤ w (u n)) :
    (∑ k ∈ Finset.range n,
      Real.exp (-(q * (times k : ℝ))) * d k) ≤ w (u 0) := by sorry
