-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_level_root_of_continuous_atTop
-- name    : AvramDividend.Classical.esscher_positive_level_root_of_continuous_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:48:09.897128+00:00
-- url     : https://prove2.me/theorems/f6d10d9c-f202-4c43-bfd9-9b0dbfdd1553
-- title:
--   Continuous shifted exponent growing to infinity admits every positive root
-- statement:
--   A real g with g(0)=0, continuous on [0,∞) and tending to positive infinity as the argument tends to infinity, attains every prescribed positive level p at a strictly positive root. This closes the analytic root existence premise of the 1E-C asymptotics under explicit continuity and growth assumptions. For g(beta)=psi(phi+beta)-q, those premises must be established for the canonical spectrally negative Levy exponent; this theorem does not assume any finite-p Wiener–Hopf factor.
-- source:
--   Pinned Mathlib.Topology.Order.IntermediateValue.intermediate_value_Ici; Kyprianou and KKR scale-functions review, Laplace-exponent convexity and positive roots.

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
open Set Filter

theorem AvramDividend.Classical.esscher_positive_level_root_of_continuous_atTop
    (g : ℝ → ℝ) (hg0 : g 0 = 0)
    (hcont : ContinuousOn g (Ici (0 : ℝ)))
    (htop : Tendsto g atTop atTop)
    (p : ℝ) (hp : 0 < p) :
    ∃ r : ℝ, 0 < r ∧ g r = p := by sorry
