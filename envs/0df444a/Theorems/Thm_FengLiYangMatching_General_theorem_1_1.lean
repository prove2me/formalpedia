-- Prove2me | Theorems.Thm_FengLiYangMatching_General_theorem_1_1
-- name    : FengLiYangMatching.General.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:00.297871+00:00
-- url     : https://prove2.me/theorems/c58cf63f-b1ed-47d0-94c1-b4fb94997249
-- title:
--   Theorem 1.1 — a 0.5445-competitive online matching algorithm
-- statement:
--   For every finite simple undirected unweighted graph G, give each edge an independent uniform [0,1] arrival time, observed on arrival. The graph and its edge count are unknown to the algorithm. Run the single transition rule Algorithm 1 with independent reservation coins of probability p=5/11, phase boundary b=3/8, and a=a*. Here a* is the unique root in (0,3/8) of L₁(a,3/8)=L₁₂(a,3/8), where
--
--   $$L_k(a,b)=\frac6{11}+\frac{(1-a)^k-(1-b)^k}{2k}-\frac{(1-a)^k}{22}-\frac{(1-b)^k}{10}\quad(k\ge1).$$
--
--   The root exists, is unique and exceeds 1/6. For every integer k≥1, L_k(a*,3/8)≥L₁(a*,3/8)>1089/2000. On every chronological loopless stream with no repeated edge, every prefix of Algorithm 1's actual output is a matching of already seen edges. Commitments persist as the prefix grows. Its final size ALG(G) is integrable and satisfies
--
--   $$\mathbb E[\operatorname{ALG}(G)]\ge\frac{1089}{2000}\operatorname{OPT}(G).$$
--
--   The expectation includes both arrival times and reservation coins, and the guarantee includes edgeless graphs. The displayed concrete witness supplies the existence claim of Theorem 1.1. Its transition sees only the current edge, timestamp, one coin and stored state; no maximum matching, graph oracle or future edge is available.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - encoding: existence of a 0.5445-competitive algorithm, witnessed by Algorithm 1 in §§1.2 and 3.2 → concrete Algorithm 1 guarantee with exact rational 1089/2000 and explicit parameter, scalar, feasibility and irrevocability conclusions; reason: the source gives this witness and establishes its scalar inequalities; all are conclusion obligations rather than assumptions
--   - encoding: expectations of finite vertex or edge counts → integrability is asserted in the conclusion together with the bound; reason: bounded measurable counts are integrable under the probability laws; this is an obligation, not an additional hypothesis
--   - encoding: continuous arrival times with shadow matching at phase boundaries → strict prefixes, half-open reserve/retain phases and fixed sorting of tied times; reason: the phases agree with Algorithm 1; arrivals at any fixed boundary and ties have probability zero; the same convention is used throughout
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Theorem 1.1, p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

/-- Theorem 1.1, witnessed by Algorithm 1 with the exact Section 3.2 parameters.
The parameter, scalar and online-feasibility clauses expose obligations rather than assumptions. -/
theorem theorem_1_1 :
    (∃! a : ℝ, Root a) ∧ Root aStar ∧ (1/6 : ℝ) < aStar ∧
    (∀ k : ℕ, 1 ≤ k → L k aStar (3/8) ≥ L 1 aStar (3/8)) ∧
    L 1 aStar (3/8) > (1089/2000 : ℝ) ∧
    (∀ n : ℕ, ∀ l : List (Edge n × ℝ × Bool),
      (l.map (fun o => o.1)).Nodup →
      (l.map (fun o => o.2.1)).Pairwise (· ≤ ·) →
      (∀ o ∈ l, ¬ o.1.IsDiag ∧ o.2.1 ∈ Set.Icc (0 : ℝ) 1) →
      ∀ j ≤ l.length,
        IsMatching (run aStar (3/8) (l.take j)).actual ∧
        (run aStar (3/8) (l.take j)).actual ⊆ ((l.take j).map (fun o => o.1)).toFinset) ∧
    (∀ n : ℕ, ∀ l : List (Edge n × ℝ × Bool),
      ∀ j k : ℕ, j ≤ k → k ≤ l.length →
        (run aStar (3/8) (l.take j)).actual ⊆ (run aStar (3/8) (l.take k)).actual) ∧
    (∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      Integrable (ALG G aStar (3/8)) (sampleLaw G (5/11)) ∧
      (∫ w, ALG G aStar (3/8) w ∂sampleLaw G (5/11)) ≥
        (1089/2000 : ℝ) * (OPT G : ℝ)) := by sorry

end FengLiYangMatching.General
