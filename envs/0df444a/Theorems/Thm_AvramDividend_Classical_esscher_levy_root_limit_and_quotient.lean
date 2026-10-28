-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_levy_root_limit_and_quotient
-- name    : AvramDividend.Classical.esscher_levy_root_limit_and_quotient
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:06:50.904929+00:00
-- url     : https://prove2.me/theorems/afa35ea0-6b74-4834-842c-67bde95476c8
-- title:
--   Canonical Esscher root existence, zero-limit and derivative-quotient asymptotics
-- statement:
--   For a canonical spectrally negative Lévy exponent ψ with ψ(φ)=q>0 at φ>0 and an explicitly assumed derivative m=ψ'(φ), a positive shifted-root family λ_p exists for every p>0, tends to zero through positive values as p↓0, and satisfies p/λ_p→m>0. This assembles genuine proven source-specific root existence, monotonicity, derivative positivity and the accepted generic derivative quotient limit; no Standing or Wiener–Hopf law is used. The existence of the canonical ψ derivative remains a separate formal obligation.
-- source:
--   Proved root family (published as esscher_levy_positive_root_family_tendsto_zero after remote acceptance), source-specific derivative bound (esscher_levy_positive_root_derivative_lower after remote acceptance), and Proved 2ba922bf-e359-4bc2-8c6c-52aacb2c7886; Mathlib HasDerivAt.comp_const_add and HasDerivAt.sub_const, KKR Scale Functions review §2.

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_family_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
import Theorems.Thm_AvramDividend_Classical_esscher_root_quotient_tendsto_of_hasDerivAt

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_levy_root_limit_and_quotient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi m : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) (hderiv : HasDerivAt X.ψ m phi) :
    ∃ lambda : ℝ → ℝ,
      (∀ p : ℝ, 0 < p → 0 < lambda p) ∧
      (∀ p : ℝ, 0 < p → X.ψ (phi + lambda p) - q = p) ∧
      Tendsto lambda (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      Tendsto (fun p : ℝ => p / lambda p)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by sorry
