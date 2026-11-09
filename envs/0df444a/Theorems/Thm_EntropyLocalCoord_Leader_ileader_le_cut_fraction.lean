-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_ileader_le_cut_fraction
-- name    : EntropyLocalCoord.Leader.ileader_le_cut_fraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:53.688384+00:00
-- url     : https://prove2.me/theorems/2ae9e7b7-d6fd-4504-8c83-8cb05bdc146f
-- title:
--   §2, p. 6 and p. 12 — $I_{\mathrm{leader}}$ is at most the edge proportion cut by a source assignment
-- statement:
--   Let $G=(N,E)$ be a finite simple graph, $\mathfrak S=(N,K,B)$ an information skeleton and $L:N\to K$ a source assignment with $L(i)\in B(i)$ for every player $i$. Then
--
--   $$I_{\mathrm{leader}}(G,\mathfrak S)\le\frac{\bigl|\{\,ij\in E: L(i)\ne L(j)\,\}\bigr|}{|E|}.$$
--
--   This is the step that turns a choice of one available source per player, with parts choosing the same source merged, into a leader profile: independent fair signs on the sources, each player copying its chosen source.
--
--   Differences from the source:
--   - encoding: the players are $N=\{1,\dots,n\}$ and the sources $K=\{1,\dots,k\}$ → the types `Fin n` and `Fin k`, indexed from 0, with $n=0$ admitted by the type; reason: a relabeling; the empty-player instance adds only a trivial case and changes no source instance
--   - encoding: an admissible partition in which each part follows a chosen common source → a source assignment $L$ with $L(i)\in B(i)$; reason: the level sets of $L$ are the merged parts, and each admissible partition with chosen sources yields such an $L$ cutting no more edges; p. 12 uses the assignment form
--   - encoding: the proportion of edges, undefined for an edgeless graph → the Lean quotient, with value 0 when $|E|=0$; reason: this only fills a case the source leaves undefined; no hypothesis on $E$ is added
--   - encoding: an arbitrary probability space and arbitrary source variables → the sample space and the source value spaces lie in Lean's universe `Type`; reason: the source fixes no universe; every measurable space used in the mathematics is represented
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272, §2, p. 6 (converse direction of the combinatorial characterization) and proof of Theorem 3.2, p. 12.

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model

namespace EntropyLocalCoord.Leader

/-- §2, p. 6 and p. 12: if every player `i` follows an available source `L i`, the leader
inefficiency is at most the proportion of edges whose endpoints follow different sources. -/
theorem ileader_le_cut_fraction {n k : ℕ} (G : SimpleGraph (Fin n))
    (S : InformationSkeleton n k) (L : Fin n → Fin k) (hL : ∀ i, L i ∈ S.B i) :
    Ileader G S ≤ cutFraction G L := by sorry

end EntropyLocalCoord.Leader
