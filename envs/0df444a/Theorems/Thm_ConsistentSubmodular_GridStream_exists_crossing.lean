-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_exists_crossing
-- name    : ConsistentSubmodular.GridStream.exists_crossing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:10.82999+00:00
-- url     : https://prove2.me/theorems/dc6e0cc8-9f8c-4ec5-93c8-e71e97d46579
-- title:
--   Intermediate crossing point of a slowly decreasing sequence
-- statement:
--   Let $b:\mathbb N\to\mathbb R$ be a sequence, $h,\delta\in\mathbb R$ and $s\le e$ natural numbers. Assume
--
--   - $b_s\ge h$ and $b_e<h$;
--   - $b_t\le b_{t+1}+\delta$ for every $t$ with $s\le t<e$ (the sequence drops by at most $\delta$ per step).
--
--   Then there is a time $t$ with $s\le t<e$ and
--   $$h\le b_t<h+\delta .$$
--
--   This is the intermediate point argument of Appendix B.1: a sequence that starts at least $h$, ends below $h$, and drops by at most $\delta$ per step must take a value in $[h,h+\delta)$ at some time in $[s,e)$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStream.lean#L33-L51 (`ConsistentSubmodular.GridStream.exists_crossing`)

import Mathlib

open scoped BigOperators
open Finset

theorem ConsistentSubmodular.GridStream.exists_crossing (b : ℕ → ℝ) {h δ : ℝ} {s e : ℕ} (hse : s ≤ e) (hs : h ≤ b s)
    (he : b e < h) (hstep : ∀ t, s ≤ t → t < e → b t ≤ b (t + 1) + δ) :
    ∃ t, s ≤ t ∧ t < e ∧ h ≤ b t ∧ b t < h + δ := by sorry
