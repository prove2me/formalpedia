-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_maximum_flow_external
-- name    : DirectedGlobalMincut.Sampling.maximum_flow_external
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:56.10402+00:00
-- url     : https://prove2.me/theorems/2702d1f4-f270-48a4-899b-68644bf99b29
-- title:
--   External input — Deterministic almost-linear maximum flow
-- statement:
--   There exists a single deterministic integer RAM program solving maximum flow on finite directed networks with nonnegative integral capacities. It has no optimization oracle and no random coins. For every fixed polynomial capacity bound and every $\varepsilon>0$, it has uniform constants and threshold giving
--
--   $$\operatorname{time}(Q)\le K_\varepsilon(|V(Q)|+|E(Q)|+2)^{1+\varepsilon}$$
--
--   above that threshold, with logarithmic-width words. All well-formed inputs terminate and receive an integral maximum flow. This exposes the cited implementation as a theorem to establish, so the standalone mincut consequence cannot be obtained merely by assuming a fast solver exists.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n and Fin m over the published arc-identity digraph, with every listed arc active; reason: enumeration preserves all finite graphs, parallel arcs and loops; it introduces no simplicity or connectivity promise
--   - encoding: an algorithm with a time bound → a finite program of the published integer RAM with actual instruction and copying costs, and logarithmic-width words; reason: the only uncharged optimization in the reduction is a correctly specified maximum-flow oracle; no arbitrary output function is assigned a cost
--   - reading: the cited deterministic almost-linear max-flow implementation → one fixed oracle-free program, with a separate uniform bound for every positive epsilon and every polynomial capacity exponent; reason: this states the full implementation obligation used by actual solver substitution, rather than a conditional hypothesis on the main input
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), unnumbered maximum-flow implementation cited immediately after Theorem 1.1, [vdBCK+23], p. 1 (PDF p. 1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_IntegerReduction

namespace DirectedGlobalMincut.Sampling

/-- Unnumbered external input on p.1, citing van den Brand et al. [vdBCK+23]. A concrete
oracle-free deterministic program is required before the standalone runtime can be closed. -/
theorem maximum_flow_external : ∃ S : IntegerProgram, FastMaximumFlow S := by sorry

end DirectedGlobalMincut.Sampling
