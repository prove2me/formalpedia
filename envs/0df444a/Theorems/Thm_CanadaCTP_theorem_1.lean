-- Prove2me | Theorems.Thm_CanadaCTP_theorem_1
-- name    : CanadaCTP.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:15.008325+00:00
-- url     : https://prove2.me/theorems/34fb5fcb-e7b8-4998-87e5-5b23afc25a78
-- title:
--   Theorem 1 — ParallelTraveller is a polynomial-time $8(e-1)/(e-2)$-approximation for CTP on disjoint-path graphs
-- statement:
--   There is a constant $C$ such that for every instance of the Stochastic Canadian Traveller Problem on a disjoint-path graph ($k\ge1$ paths, each with at least one edge, independent explicit finite non-negative edge distributions), the ParallelTraveller policy
--
--   1. reaches $t$ with probability $1$;
--   2. has expected cost
--   $$
--   \mathbb E[\mathrm{Alg}]\ \le\ \frac{8(e-1)}{e-2}\,\mathbb E[\mathrm{Opt}]\approx 19.138\,\mathbb E[\mathrm{Opt}],
--   $$
--   where $\mathbb E[\mathrm{Opt}]$ is the infimum of the expected cost over all randomized adaptive policies, of any memory, that reach $t$ almost surely;
--   3. performs, on every run, at most $C\,(1+\max(\log|E|,\log M))\sum_i d_i\max(d_i,\log k)$ operations (Theorem 3).
--
--   This is the first constant-factor approximation for CTP on disjoint-path graphs.
--
--   **Formalization Note** "O(1)" is the constant of the proof (p.19); "polynomial-time" is Theorem 3's bound on the policy's operation counter. Every traversal of an edge is paid, including the walks back to $s$.
--
--   Differences from the source:
--   - generalization: "There is a … O(1)-approximation algorithm" → the named policy ptPolicy (Algorithm 1) with the explicit ratio 8(e−1)/(e−2); reason: the proof's algorithm and constant (p.19); this implies the existence of an O(1)-approximation
--   - generalization: E[Opt] over adaptive policies (deterministic, "determines … which edge should be traversed next") → infimum over all feasible randomized stateful policies of every memory type; reason: a larger class gives a smaller infimum, so the bound is stronger; deterministic history-dependent policies are the case Mem = histories with point-mass steps
--   - encoding: polynomial-time → Theorem 3's explicit bound on the operation counter ops, ∃ C before the instance; reason: unit-cost operation count of the named policy (see Theorem 3)
--   - encoding: an algorithm for CTP (reaches t) → Feasible I (ptPolicy I): arrival probability 1; reason: a CTP policy must reach t
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - generalization: disjoint-path graphs (graphs, union of internally vertex-disjoint s–t paths) → any k ≥ 1 paths with m_i ≥ 1 edges, parallel one-edge paths allowed (a multigraph); reason: every disjoint-path graph is such an instance, so the statement specializes to the source
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 1, p.3 (restated p.18); proof pp.18–19; the constant p.19

import Mathlib
import Definitions.Def_CanadaCTP_ParallelTraveller

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Theorem 1, p.3 (restated p.18, proof pp.18–19): ParallelTraveller is a
polynomial-time `8(e−1)/(e−2)`-approximation for CTP on disjoint-path graphs. For every instance
(at least one path, every path with at least one edge):
1. it reaches `t` almost surely;
2. its expected cost is at most `8(e−1)/(e−2) ≈ 19.138` times `E[Opt]`, the infimum of the
   expected cost over all feasible randomized stateful adaptive policies;
3. on every run its counted operations are at most `C·(1 + max(log |E|, log M))·Σᵢ dᵢ·max(dᵢ, log k)`
   (Theorem 3), with one constant `C` for all instances.

**Formalization Note.** "O(1)" is the proof's explicit constant (p.19); "polynomial time" is
Theorem 3's bound on the operation counter of the policy. -/
theorem theorem_1 : ∃ C : ℝ, ∀ I : Inst, I.IsCTP →
    Feasible I (ptPolicy I) ∧
    expCost I (ptPolicy I) ≤
      ENNReal.ofReal (8 * (Real.exp 1 - 1) / (Real.exp 1 - 2)) * optCost I ∧
    ∀ (ι : Realz I) (N : ℕ), ∀ cfg ∈ (lawN I (ptPolicy I) ι N).support,
      (cfg.mem.ops : ℝ) ≤ C * (1 + max (Real.log (nE I)) (Real.log (Mbig I))) *
        ∑ i, (dsz I i : ℝ) * max (dsz I i : ℝ) (Real.log I.k) := by sorry

end CanadaCTP
