-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_theorem_3_2
-- name    : EntropyLocalCoord.Leader.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:14.187807+00:00
-- url     : https://prove2.me/theorems/cc6c3efd-2536-42bf-b769-87c85a738ea1
-- title:
--   Theorem 3.2 — $I_{\mathrm{leader}}(G,\mathfrak S)\le2h(\tfrac12I_{\mathrm{bin}}(G,\mathfrak S))$
-- statement:
--   For every finite simple graph $G=(N,E)$ and every information skeleton $\mathfrak S=(N,K,B)$,
--
--   $$I_{\mathrm{leader}}(G,\mathfrak S)\le2h\bigl(\tfrac12I_{\mathrm{bin}}(G,\mathfrak S)\bigr),$$
--
--   where $h(p)=-p\log_2p-(1-p)\log_2(1-p)$ is the binary entropy function, with $0\log0=0$. Here $I_{\mathrm{bin}}$ and $I_{\mathrm{leader}}$ are the infima of the discoordination cost over the binary and the leader coordination profiles adapted to $\mathfrak S$, with arbitrary independent sources on an arbitrary probability space.
--
--   This is the paper's main theorem: for binary outputs, the loss from restricting to leader strategies is logarithmic rather than a square root.
--
--   Differences from the source:
--   - encoding: the players are $N=\{1,\dots,n\}$ and the sources $K=\{1,\dots,k\}$ → the types `Fin n` and `Fin k`, indexed from 0, with $n=0$ admitted by the type; reason: a relabeling; the empty-player instance adds only a trivial case and changes no source instance
--   - encoding: $C(G,\pi)$ divides by $|E|$, undefined for an edgeless graph → the Lean quotient, with value 0 when $|E|=0$; reason: this only fills a case the source leaves undefined; no hypothesis on $E$ is added
--   - encoding: an arbitrary probability space and arbitrary source variables → the sample space and the source value spaces lie in Lean's universe `Type`; reason: the source fixes no universe; every measurable space used in the mathematics is represented
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272, Theorem 3.2 and footnote 3, p. 7; proof in §4, pp. 10–12.

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model

namespace EntropyLocalCoord.Leader

/-- Theorem 3.2, p. 7: for every graph `G` and every information skeleton `𝔖`,
`I_leader(G, 𝔖) ≤ 2 h(½ I_bin(G, 𝔖))`, with `h` the binary entropy function in bits. -/
theorem theorem_3_2 {n k : ℕ} (G : SimpleGraph (Fin n)) (S : InformationSkeleton n k) :
    Ileader G S ≤ 2 * h (1 / 2 * Ibin G S) := by sorry

end EntropyLocalCoord.Leader
