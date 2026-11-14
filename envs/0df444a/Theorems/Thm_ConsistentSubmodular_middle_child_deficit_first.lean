-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_child_deficit_first
-- name    : ConsistentSubmodular.middle_child_deficit_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:06.963204+00:00
-- url     : https://prove2.me/theorems/8d3ff0f3-1711-4feb-b384-fedb6c49fc5b
-- title:
--   Middle child deficit bound, first range ($p\in[\tfrac{19}{80},\tfrac3{10}]$)
-- statement:
--   Let $q,d,p,\delta$ be real numbers with $1\le q\le \tfrac43$ and $\delta\ge 0$. Assume
--   $$0\le (36-25q+3q^2)\,d-(3-q)(3-2q)-q(4-q)\,p-q^2\delta .$$
--   If moreover $\tfrac{19}{80}\le p\le \tfrac{3}{10}$, then
--   $$d\;\ge\;\frac{2}{25}+\frac{2p}{5}.$$
--
--   This is a purely scalar lower bound on the deficit parameter $d$ extracted from the middle-parent credit inequality; it is one of the elementary real-variable inputs of the middle-parent analysis in the deterministic certificate construction (applied for the range $p\le 3/10$).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSources.lean#L49-L73 (`ConsistentSubmodular.middle_child_deficit_first`)

import Mathlib

theorem ConsistentSubmodular.middle_child_deficit_first (q d p δ : ℝ)
    (_hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hpl : (19 : ℝ) / 80 ≤ p) (hpu : p ≤ 3 / 10)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 2 / 25 + 2 * p / 5 ≤ d := by sorry
