-- Prove2me | Theorems.Thm_ConsistentSubmodular_exp_moment_step
-- name    : ConsistentSubmodular.exp_moment_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:52.432198+00:00
-- url     : https://prove2.me/theorems/6f8b118f-aab9-41dc-bb75-cde385dbe933
-- title:
--   Scalar step of the exponential-moment induction
-- statement:
--   Let $\lambda,p,\delta,d\in\mathbb R$ with $p\ge 0$, $0\le\delta\le d\le 1$. Then
--
--   $$(1-p)+p\cdot\exp\!\Big(-\lambda d+(\delta-d)\big(e^{-\lambda}-1\big)\Big)\;\le\;\exp\!\Big(p\,\delta\,\big(e^{-\lambda}-1\big)\Big).$$
--
--   In the induction over the coordinates of an independent sample, $\delta$ is the mean marginal value of a coordinate, $d$ is its marginal at the empty set, and $p$ the probability that the coordinate is selected. The inequality is the scalar estimate for one coordinate.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ExponentialTails.lean#L51-L95 (`ConsistentSubmodular.exp_moment_step`)

import Mathlib

open scoped BigOperators

theorem ConsistentSubmodular.exp_moment_step {lam p δ d : ℝ} (hp0 : 0 ≤ p)
    (hδ0 : 0 ≤ δ) (hδd : δ ≤ d) (hd1 : d ≤ 1) :
    (1 - p) + p * Real.exp (-lam * d + (δ - d) * (Real.exp (-lam) - 1)) ≤
      Real.exp (p * δ * (Real.exp (-lam) - 1)) := by sorry
