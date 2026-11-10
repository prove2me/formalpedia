-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_3_1
-- name    : FengLiYangMatching.General.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:16.928748+00:00
-- url     : https://prove2.me/theorems/ab1825d7-ad5d-4314-b72a-17d38351307c
-- title:
--   Lemma 3.1 — finite convex expansion of Greedy survival
-- statement:
--   Let J be any finite simple graph with independent uniform [0,1] edge arrival times, and A any set of vertices, including the empty set. Write P(J,A,t) for the actual probability that all vertices of A are unmatched by Greedy at time t. There is one finitely supported coefficient family c_k≥0, chosen independently of t, such that
--
--   $$\sum_{k\ge0}c_k=1,\qquad P(J,A,t)=\sum_{k\ge0}c_k(1-t)^k\quad(0\le t\le1).$$
--
--   The constant term is permitted, including at t=1 with 0⁰=1. Applied to J=G−e and A the endpoints of e, this supplies the survival expansions needed in the ratio analysis.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - encoding: indices n≥1 with exponent n−1 → finitely supported coefficients indexed by k≥0 with exponent k; reason: the bijection k=n−1 removes Nat subtraction and preserves every term including the constant
--   - reading: there exist coefficients in the statement mentioning t → one common coefficient family works simultaneously for all t∈[0,1]; reason: the recursive proof and Eqs. (7)–(8), p. 11 construct coefficients for the entire survival function
--   - encoding: continuous arrival times with shadow matching at phase boundaries → strict prefixes, half-open reserve/retain phases and fixed sorting of tied times; reason: the phases agree with Algorithm 1; arrivals at any fixed boundary and ties have probability zero; the same convention is used throughout
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 3.1, p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_3_1 {n : ℕ} (J : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    ∃ c : ℕ →₀ ℝ, (∀ k, 0 ≤ c k) ∧ c.sum (fun _ v => v) = 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        survival J A t = c.sum (fun k v => v * (1-t)^k) := by sorry

end FengLiYangMatching.General
