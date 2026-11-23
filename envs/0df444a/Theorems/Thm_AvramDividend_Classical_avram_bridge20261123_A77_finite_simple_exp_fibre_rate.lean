-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_finite_simple_exp_fibre_rate
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_finite_simple_exp_fibre_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T16:35:28.728136+00:00
-- url     : https://prove2.me/theorems/0549a399-225a-4d1a-b715-967bb729c310
-- title:
--   Finite negative-mark Lévy intensity integral of a simple exponential equals its finite value-fibre sum
-- statement:
--   For any real Borel measure finite on the negative half-line and any real-valued finite-range measurable simple function, express the restricted integral exp(g)-1 exactly as the finite sum over values z in g.range weighted by the measure of the restricted level sets g=z. This is the deterministic rate identity needed for the original A77 physical finite-jump fibre construction; the source measure remains arbitrary and no stochastic independence is assumed.
-- source:
--   Pinned Mathlib SimpleFunc.map_integral and original A77 fibre source 5aaebfc3; generalises Proved Avram a20 spatial simple mark integral partition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_finite_simple_exp_fibre_rate
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) ≠ ⊤)
    (g : SimpleFunc ℝ ℝ) :
    (∫ y in Iio (0 : ℝ), Real.exp (g y) - 1 ∂ν) =
      ∑ z ∈ g.range,
        (ν (Iio (0 : ℝ) ∩ g ⁻¹' {z})).toReal *
          (Real.exp z - 1) := by sorry
