-- Prove2me | Theorems.Thm_ConsistentSubmodular_RoundingBudget_bridge_value_budget_exp
-- name    : ConsistentSubmodular.RoundingBudget.bridge_value_budget_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:17.708209+00:00
-- url     : https://prove2.me/theorems/0171629e-787e-47a0-b448-4f8d727abe88
-- title:
--   Per-test probability budget for the bridge value lower tail
-- statement:
--   Let $B,N,c,H\in\mathbb N$ with $B,N,H>0$ and let $V>0$ be real. Assume $4B\le 2^c$ and $8N^2c\le H$. Then
--
--   $$\exp\!\Big(-\frac{(V/N)^2}{2\,(2V/H)\,(2V)}\Big)\;\le\;\frac1{4B}.$$
--
--   This is the bridge lower tail with deviation $V/N$, marginal cap $2V/H$ and mean bound $2V$ (the concentration bound of equation (37)); it fits the per-test budget $1/(4B)$ once $H\ge 8N^2c$ and $4B\le 2^c$. It is an arithmetic inequality used to check the probability budget in the rounding of bridges.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/RoundingBudget.lean#L70-L89 (`ConsistentSubmodular.RoundingBudget.bridge_value_budget_exp`)

import Mathlib

theorem ConsistentSubmodular.RoundingBudget.bridge_value_budget_exp (B N c H : ℕ) (V : ℝ) (hB : 0 < B) (hN : 0 < N)
    (hV : 0 < V) (hH0 : 0 < H) (hc : 4 * B ≤ 2 ^ c) (hH : 8 * N ^ 2 * c ≤ H) :
    Real.exp (-((V / N) ^ 2) / (2 * (2 * V / H) * (2 * V))) ≤ 1 / (4 * B) := by sorry
