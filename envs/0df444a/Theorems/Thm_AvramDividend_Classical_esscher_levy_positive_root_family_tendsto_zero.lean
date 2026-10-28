-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_family_tendsto_zero
-- name    : AvramDividend.Classical.esscher_levy_positive_root_family_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:57:27.610922+00:00
-- url     : https://prove2.me/theorems/868634e8-298b-4df9-8c8a-f7f053c4dbc5
-- title:
--   Canonical Esscher positive root family exists and vanishes as its level decreases to zero
-- statement:
--   For the actual spectrally negative Lévy exponent ψ with ψ(φ)=q>0 at φ>0, there exists a positive root-selection family λ_p for all p>0 such that ψ(φ+λ_p)−q=p and λ_p tends to zero through positive values as p↓0. This uses already-Proved source-specific root existence and strict increase and the accepted generic inverse-root convergence theorem, without additional Standing or derivative assumptions.
-- source:
--   Proved a9d8fdb2-917c-4ec8-992f-fa0ba374c16b (unrestricted genuine shifted roots), 0906e33f-37dc-4382-95d0-b5cad94b12ab (actual strict increase), and e746f729-2b86-4a36-961f-c65553d3ba44 (positive inverse-root limit); Kuznetsov–Kyprianou–Rivero, Scale Functions review §2.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.NhdsWithin
import Mathlib.Order.Monotone.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_shift_positive_root_of_levy_secant
import Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_strictMonoOn
import Theorems.Thm_AvramDividend_Classical_esscher_root_tendsto_zero_of_strictMonoOn

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_levy_positive_root_family_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) :
    ∃ lambda : ℝ → ℝ,
      (∀ p : ℝ, 0 < p → 0 < lambda p) ∧
      (∀ p : ℝ, 0 < p → X.ψ (phi + lambda p) - q = p) ∧
      Tendsto lambda (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhdsWithin (0 : ℝ) (Ioi 0)) := by sorry
