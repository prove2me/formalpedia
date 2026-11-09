-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_rooted_approximation_external
-- name    : DirectedGlobalMincut.Sampling.rooted_approximation_external
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:07.515973+00:00
-- url     : https://prove2.me/theorems/e8ec00f2-32e4-49b2-bf80-16ec1916702a
-- title:
--   External input — Rooted approximation cited on p.3
-- statement:
--   For every fixed polynomial input bound and confidence exponent $a\ge1$, a uniform randomized maximum-flow oracle program returns a rooted cut of weight $C$. With probability at least $1-n^{-a}$,
--
--   $$\lambda\le C\le\frac54\lambda,$$
--
--   where $\lambda$ is the rooted minimum-cut weight. The program uses $O(\log^4 n)$ maximum-flow calls on $O(m)$-size instances and near-linear additional work. Its input contains the graph, weights and root, not $\lambda$. All outcomes halt with a valid rooted cut. This is the genuine external algorithm contract cited by the canonical PDF; it remains an open supporting obligation of this mission.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n and Fin m over the published arc-identity digraph, with every listed arc active; reason: enumeration preserves all finite graphs, parallel arcs and loops; it introduces no simplicity or connectivity promise
--   - encoding: an algorithm with a time bound → a finite program of the published integer RAM with actual instruction and copying costs, and logarithmic-width words; reason: the only uncharged optimization in the reduction is a correctly specified maximum-flow oracle; no arbitrary output function is assigned a cost
--   - reading: with high probability and the stated asymptotic bounds → arbitrary inverse-polynomial confidence and uniform programs/constants for every fixed polynomial-bound exponent; reason: this is the same confidence convention as the main target and permits a separate approximation failure budget
--   - encoding: lambda<=C<=5lambda/4 → a valid cut of weight C and C<=5/4 times the weight of every valid rooted cut; reason: this is equivalent to the minimum-weight formulation on the finite nonempty rooted-cut domain and avoids an empty or unbounded infimum
--   - encoding: a cut separating distinct vertices, or a nonempty root-excluding cut → the input domain requires n>=2; reason: below two vertices the claimed cut does not exist; this excludes only undefined cut instances
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), unnumbered external input in the proof of Theorem 1.1, citing [Qua26, Theorem 3.4], p. 3 (PDF p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_IntegerReduction

namespace DirectedGlobalMincut.Sampling

/-- Unnumbered external input on p.3, citing Quanrud, Theorem 3.4. This is a target to establish,
not an assumed fast rooted-mincut primitive. -/
theorem rooted_approximation_external : RootedApproximationTarget := by sorry

end DirectedGlobalMincut.Sampling
