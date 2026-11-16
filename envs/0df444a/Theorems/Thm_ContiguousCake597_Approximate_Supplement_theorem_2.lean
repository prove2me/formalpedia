-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_Supplement_theorem_2
-- name    : ContiguousCake597.Approximate.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:01:05.895235+00:00
-- url     : https://prove2.me/theorems/4fb01531-443e-4706-bb4b-c796e358fd1b
-- title:
--   Theorem 2 — PPAD-completeness of contiguous EFc and EFc-outer for goods on a path
-- statement:
--   Consider $n\ge1$ agents and $m$ goods $g_1,\dots,g_m$ on a path, with nonnegative rational additive valuations. Let the removal budget $c$ be either
--
--   1. a fixed integer $c\ge1$, or
--   2. $c=\lfloor m^\alpha\rfloor$ for a fixed rational $0<\alpha<1$, where $m$ is the number of goods.
--
--   For each such budget and for each of the two notions EF$c$ and EF$c_{\mathrm{outer}}$, the search problem of computing a contiguous allocation satisfying the notion is PPAD-complete:
--   $$\textsc{EF}c\text{-Path},\ \textsc{EF}c_{\mathrm{outer}}\text{-Path}\ \text{are PPAD-complete}.$$
--   Moreover the same holds for the restriction to binary valuations in which every good is valued by exactly one agent and all agents value the same number of goods. PPAD membership is in the sense of §2.1 (total, reducible to End-of-Line, polynomial-time verifiable, polynomial-length answers), and hardness means that every problem in PPAD reduces to the problem by a polynomial-time search reduction. This covers all eight combinations of budget type, fairness notion and instance class.
--
--   This companion result to Theorem 1 classifies the complexity of contiguous EF$c$ allocations of indivisible goods with a flexible agent order.
--
--   Differences from the source:
--   - encoding: PPAD-complete → the published PPAD predicate with a polynomial-time verifier and short-witness existence, plus hardness with respect to the published class PPAD; reason: the paper's definition of PPAD in §2.1 includes the verifier and witness requirements
--   - generalization: "the hardness holds even for" the binary exclusive equal-count class → the restricted relation is stated PPAD-complete, membership included; reason: the restricted relation has the same answers on fewer valid inputs, so its totality, End-of-Line reduction and short answers follow from the general relation's, and its verifier adds only a polynomial-time check of the class; the statement contains the source's claim (general completeness, restricted hardness)
--   - encoding: c = ⌊m^α⌋ → the largest h ≤ m with h^q ≤ m^p for α = p/q in lowest terms; reason: equal to ⌊m^α⌋ for every m when 0 < α < 1
--   - reading: n agents → n ≥ 1 agents; reason: the paper's standing convention; with no agents and at least one good no allocation exists
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 2 (PDF 3), Theorem 2; proof p. 13 (PDF 14)

import Definitions.Def_ContiguousCake597_Approximate_Supplement_Path

namespace ContiguousCake597.Approximate.Supplement

/-- Theorem 2, printed p.2 (PDF 3), proof printed p.13 (PDF 14). PPAD-completeness of
contiguous goods EFc and EFc_outer search, for each fixed `c ≥ 1` and for `c = ⌊m^α⌋`
with each fixed rational `0 < α < 1`, both for general nonnegative rational valuations
and for the binary exclusive-ownership equal-count class. -/
theorem theorem_2 :
    (∀ c : ℕ, 1 ≤ c → ∀ outer restricted : Bool,
      PaperPPADComplete (PathProblem false outer (.const c) restricted)) ∧
    (∀ α : ℚ, 0 < α → α < 1 → ∀ outer restricted : Bool,
      PaperPPADComplete (PathProblem false outer (.power α) restricted)) := by sorry

end ContiguousCake597.Approximate.Supplement
