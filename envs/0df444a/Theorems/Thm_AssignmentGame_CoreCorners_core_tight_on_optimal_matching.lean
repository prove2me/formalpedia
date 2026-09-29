-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_core_tight_on_optimal_matching
-- name    : AssignmentGame.CoreCorners.core_tight_on_optimal_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:23:31.814542+00:00
-- url     : https://prove2.me/theorems/712d86fb-7f9f-4cfb-a0fe-66ee1a6650ee
-- title:
--   Sec. 3.3, proof of the Lemma — core payoffs are tight on an optimal assignment and zero off it
-- statement:
--   Let $M$ (sellers) and $N$ (buyers) be finite sets and $a_{ij} \ge 0$. Let $P \subseteq M \times N$ be an **optimal assignment**: a matching (no seller and no buyer in two pairs of $P$) whose total gain equals the worth of the all-player coalition,
--   $$\sum_{(i,j) \in P} a_{ij} = \operatorname{worth}(M, N).$$
--   Then every core vector $(u, v)$ satisfies
--
--   1. $u_i + v_j = a_{ij}$ for every pair $(i, j) \in P$;
--   2. $u_i = 0$ for every seller $i$ not assigned by $P$;
--   3. $v_j = 0$ for every buyer $j$ not assigned by $P$.
--
--   This is the step of the proof of the Lemma (p. 121) where, after labelling the optimal assignment as $11, 22, \dots, kk$, the authors use $u_i = a_{ii} - v_i$ for $i \le k$ and $u_i = v_j = 0$ for $i, j > k$. It is what turns the lattice operations of the Lemma into core vectors that exhaust $\operatorname{worth}(M, N)$.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 121, Sec. 3.3, proof of the Lemma

import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game

open Finset

namespace AssignmentGame.CoreCorners

/-- Sec. 3.3, proof of the Lemma, p. 121: on an optimal assignment `P` every core vector splits
each `a i j`, `(i, j) ∈ P`, exactly between the two partners, and pays zero to every player not
assigned by `P`. -/
theorem core_tight_on_optimal_matching {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (P : Finset (M × N)) (hP : IsMatching Finset.univ Finset.univ P)
    (hopt : ∑ p ∈ P, a p.1 p.2 = worth a Finset.univ Finset.univ)
    (u : M → ℝ) (v : N → ℝ) (huv : (u, v) ∈ core a) :
    (∀ p ∈ P, u p.1 + v p.2 = a p.1 p.2) ∧
    (∀ i : M, (∀ p ∈ P, p.1 ≠ i) → u i = 0) ∧
    (∀ j : N, (∀ p ∈ P, p.2 ≠ j) → v j = 0) := by sorry

end AssignmentGame.CoreCorners
