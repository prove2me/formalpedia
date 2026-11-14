-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_child_deficit_second
-- name    : ConsistentSubmodular.middle_child_deficit_second
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:30.779401+00:00
-- url     : https://prove2.me/theorems/0157289c-ae72-4590-9b20-91c01f2f9c68
-- title:
--   Middle child deficit bound, second range ($p\in[\tfrac3{10},\tfrac12]$)
-- statement:
--   Let $q,d,p,\delta$ be real numbers with $1\le q\le \tfrac43$ and $\delta\ge 0$. Assume
--   $$0\le (36-25q+3q^2)\,d-(3-q)(3-2q)-q(4-q)\,p-q^2\delta .$$
--   If moreover $\tfrac{3}{10}\le p\le \tfrac{1}{2}$, then
--   $$d\;\ge\;\frac{1}{8}+\frac{p}{4}.$$
--
--   This is a purely scalar lower bound on the deficit parameter $d$ extracted from the middle-parent credit inequality; it complements the bound for $p\le 3/10$ in the middle-parent analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSources.lean#L75-L98 (`ConsistentSubmodular.middle_child_deficit_second`)

import Mathlib

theorem ConsistentSubmodular.middle_child_deficit_second (q d p δ : ℝ)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hpl : (3 : ℝ) / 10 ≤ p) (hpu : p ≤ 1 / 2)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 1 / 8 + p / 4 ≤ d := by sorry
