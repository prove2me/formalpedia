-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_renewal_laplace_geometric_series
-- name    : AvramDividend.Classical.scale_renewal_laplace_geometric_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:16:38.576197+00:00
-- url     : https://prove2.me/theorems/7b29351d-b015-4a0f-85e7-f3e976a41d06
-- title:
--   Geometric Laplace mass of positive-discount scale renewal powers
-- statement:
--   The candidate q-scale function constructed as the sum of zero-discount causal convolution powers has geometric Laplace transform 1/(psi-q), provided 0<=q<psi. This is the algebraic end of the constructive positive-discount scale-function existence proof and isolates the exact domain condition on the Laplace exponent.
-- source:
--   Mathlib hasSum_geometric_of_lt_one, HasSum.mul_left and inverse arithmetic; Behme, Oechsler and Schilling (2022) convolution series for q-scale functions.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open AvramDividend.Classical

theorem AvramDividend.Classical.scale_renewal_laplace_geometric_series
    (q ψ : ℝ) (hq : 0 ≤ q) (hψ : 0 < ψ) (hqψ : q < ψ) :
    (∑' n : ℕ, q ^ n * (ψ⁻¹) ^ (n + 1)) = (ψ - q)⁻¹ := by sorry
