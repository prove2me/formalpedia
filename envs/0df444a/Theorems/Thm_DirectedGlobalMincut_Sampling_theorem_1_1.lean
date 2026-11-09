-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_theorem_1_1
-- name    : DirectedGlobalMincut.Sampling.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:48.744667+00:00
-- url     : https://prove2.me/theorems/577c97f6-eba2-4c92-a11c-06aacbf2d7fe
-- title:
--   Theorem 1.1 — Exact directed global mincut and standalone runtime
-- statement:
--   Let $G$ have $n\ge2$ vertices, $m\ge n$ arc identities, and positive integral weights $1\le w_e\le W$. For every fixed polynomial bound $m,W\le n^b$ and every confidence exponent $a\ge1$, one uniform randomized program returns an exact global minimum cut with
--
--   $$\Pr[\text{minimum cut returned}]\ge1-n^{-a}.$$
--
--   It uses maximum-flow instances with total vertices plus arcs at most $\lceil K m\log^k(2+n)\rceil$ and at most that much additional executed work. The program and constants precede every input graph, and all random outcomes terminate with a valid nonempty proper cut. Strong connectivity is not assumed; zero cuts are included.
--
--   The same theorem existentially establishes a deterministic almost-linear max-flow implementation and substitutes it through an actual caller/callee execution. The resulting standalone algorithm has, for every $\varepsilon>0$, uniform constants $K_\varepsilon,N_\varepsilon$ with
--
--   $$\operatorname{time}\le K_\varepsilon m^{1+\varepsilon}\qquad(m\ge N_\varepsilon),$$
--
--   while retaining the success guarantee and logarithmic-width words. Small inputs also terminate. This includes the sentence immediately following Theorem 1.1 in the canonical PDF.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n and Fin m over the published arc-identity digraph, with every listed arc active; reason: enumeration preserves all finite graphs, parallel arcs and loops; it introduces no simplicity or connectivity promise
--   - encoding: an algorithm with a time bound → a finite program of the published integer RAM with actual instruction and copying costs, and logarithmic-width words; reason: the only uncharged optimization in the reduction is a correctly specified maximum-flow oracle; no arbitrary output function is assigned a cost
--   - reading: polynomially bounded inputs, soft-O(m), and with high probability → for every b,a>=1, one program and graph-independent K,k with probability at least 1-n^(-a) and both resource bounds on every execution; reason: this unpacks the source asymptotics and the p.3 amplification without fixing a weaker confidence or a particular logarithmic exponent; constants absorb smaller well-formed inputs
--   - encoding: the randomized algorithm can fail on exceptional random choices → every choice terminates with a valid cut, with optimality only required with high probability; reason: bounded failure branches and a fixed valid fallback cut complete the algorithm on bad approximation or sampling outcomes without assuming a good event
--   - encoding: using the cited almost-linear maximum-flow implementation yields m^(1+o(1)) time → existence of an actual deterministic solver and a charged two-procedure substitution, with one program satisfying every m^(1+epsilon) asymptotic bound; reason: the standalone consequence is unconditional and the solver cost is actually executed, not supplied by a transcript or an assumed runtime label
--   - encoding: a cut separating distinct vertices, or a nonempty root-excluding cut → the input domain requires n>=2; reason: below two vertices the claimed cut does not exist; this excludes only undefined cut instances
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Theorem 1.1 and immediately following runtime consequence, p. 1 (PDF p. 1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_IntegerReduction

namespace DirectedGlobalMincut.Sampling

/-- Theorem 1.1 and its immediately following standalone consequence (p.1).
FullMincutTarget expands into uniform operational programs, probability, both resource bounds,
and actual substitution of an existentially established deterministic almost-linear max-flow solver. -/
theorem theorem_1_1 : FullMincutTarget := by sorry

end DirectedGlobalMincut.Sampling
