-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_integral_sum_shift
-- name    : ConsistentSubmodular.Shadow.integral_sum_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:20.406342+00:00
-- url     : https://prove2.me/theorems/f8d6b6ab-e009-4ea5-9bf1-8c8f82a8fdd6
-- title:
--   Averaging translates: $\int_0^1\sum_{j<N}\varphi(s+j)\,ds=\int_0^N\varphi$
-- statement:
--   Let $\varphi:\mathbb R\to\mathbb R$ be measurable and bounded, $|\varphi(x)|\le C$ for all $x$, and let $N\in\mathbb N$. Then
--   $$\int_0^1\sum_{j=0}^{N-1}\varphi(s+j)\,ds\;=\;\int_0^N\varphi(y)\,dy.$$
--
--   Averaging the sum of the $N$ unit translates of $\varphi$ over the offset $s\in[0,1]$ recovers the integral of $\varphi$ over $[0,N]$. It is used to pass from a discrete sum over a chain to an integral in the shadow-chain argument.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L36-L50 (`ConsistentSubmodular.Shadow.integral_sum_shift`)

import Mathlib

open scoped BigOperators Topology
open MeasureTheory Filter Set

theorem ConsistentSubmodular.Shadow.integral_sum_shift {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C)
    (N : ℕ) : ∫ s in (0 : ℝ)..1, ∑ j ∈ Finset.range N, φ (s + j) = ∫ y in (0 : ℝ)..N, φ y := by sorry
