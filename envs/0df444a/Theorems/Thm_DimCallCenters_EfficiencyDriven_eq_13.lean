-- Prove2me | Theorems.Thm_DimCallCenters_EfficiencyDriven_eq_13
-- name    : DimCallCenters.EfficiencyDriven.eq_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:42:10.872384+00:00
-- url     : https://prove2.me/theorems/fa74c30a-9a53-4443-b704-d251cc7a3707
-- title:
--   Equation (13) — convex staffing cost preserves separation
-- statement:
--   Let $F$ be convex and strictly increasing, and let $a_\lambda,b_\lambda$ be positive staffing offsets. If the ratio $a_\lambda/b_\lambda$ has limsup greater than one, then the ratio of incremental staffing costs does too:
--
--   $$
--   \limsup_{\lambda\to\infty}\frac{a_\lambda}{b_\lambda}>1
--   \quad\Longrightarrow\quad
--   \limsup_{\lambda\to\infty}\frac{F_\lambda(a_\lambda)}{F_\lambda(b_\lambda)}>1.
--   $$
--
--   The report uses this comparison when ruling out a positive limiting offset in the efficiency-driven regime.
--
--   **Formalization Note** A real-filter frequent-occurrence statement expresses each strict limsup inequality without requiring a globally defined real limsup.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 16, Eq. (13)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam

open Filter

namespace DimCallCenters.EfficiencyDriven

/-- Equation (13), p. 16: a limsup separation is preserved by
the increasing convex staffing-cost function. -/
theorem eq_13 (μ : ℝ) (F : ℝ → ℝ) (a b : ℝ → ℝ)
    (hμ : 0 < μ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (ha : ∀ lam, 0 < lam → 0 < a lam)
    (hb : ∀ lam, 0 < lam → 0 < b lam)
    (hsep : ∃ c : ℝ, 1 < c ∧ ∃ᶠ lam in atTop, c ≤ a lam / b lam) :
    ∃ c : ℝ, 1 < c ∧
      ∃ᶠ lam in atTop,
        c ≤ DimCallCenters.Rationalized.Flam F μ lam (a lam) / DimCallCenters.Rationalized.Flam F μ lam (b lam) := by sorry

end DimCallCenters.EfficiencyDriven
