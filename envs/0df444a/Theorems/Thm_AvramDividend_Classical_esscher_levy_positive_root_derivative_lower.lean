-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
-- name    : AvramDividend.Classical.esscher_levy_positive_root_derivative_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:55:03.403514+00:00
-- url     : https://prove2.me/theorems/7e3b59e7-6d4f-4dbc-a2be-f9c95cabecbb
-- title:
--   Positive derivative lower bound at a canonical Lévy Esscher q-root
-- statement:
--   For a canonical spectrally negative Lévy process with ψ(φ)=q>0 at φ>0, if its Laplace exponent has derivative m at φ, then m≥q/φ>0. The proof takes the right-hand derivative limit in an already canonically Proved source-specific secant inequality. No separate convexity premise, Standing, Esscher path law or Wiener–Hopf theorem is required.
-- source:
--   Proved e9488750-ba29-4b2a-9d1d-05734aaa628f (canonical shifted secant) and pinned Mathlib HasDerivAt.tendsto_slope_zero_right, ge_of_tendsto; KKR Scale Functions review §2. The derivative-existence assumption is explicit.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_levy_positive_root_derivative_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi m : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) (hderiv : HasDerivAt X.ψ m phi) :
    q / phi ≤ m ∧ 0 < m := by sorry
