-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_ileader_le_entropy_cost
-- name    : EntropyLocalCoord.Leader.ileader_le_entropy_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:17.514448+00:00
-- url     : https://prove2.me/theorems/16cf7dd3-97f1-49b6-9dd8-757040846d7d
-- title:
--   Proof of Theorem 3.2, p. 12 — $I_{\mathrm{leader}}\le2h(\tfrac12C(G,\pi))$ for every binary profile
-- statement:
--   Let $G=(N,E)$ be a finite simple graph, $\mathfrak S=(N,K,B)$ an information skeleton and $\pi$ a binary coordination profile adapted to $\mathfrak S$. Then
--
--   $$I_{\mathrm{leader}}(G,\mathfrak S)\le2h\bigl(\tfrac12C(G,\pi)\bigr),$$
--
--   where $C(G,\pi)$ is the discoordination cost of $\pi$ and $h$ is the binary entropy function in bits.
--
--   This is the per-profile form of the main theorem, and the last step before passing to the infimum over binary profiles.
--
--   Differences from the source:
--   - encoding: the players are $N=\{1,\dots,n\}$ and the sources $K=\{1,\dots,k\}$ → the types `Fin n` and `Fin k`, indexed from 0, with $n=0$ admitted by the type; reason: a relabeling; the empty-player instance adds only a trivial case and changes no source instance
--   - encoding: $C(G,\pi)$ divides by $|E|$, undefined for an edgeless graph → the Lean quotient, with value 0 when $|E|=0$; reason: this only fills a case the source leaves undefined; no hypothesis on $E$ is added
--   - encoding: an arbitrary probability space and arbitrary source variables → the sample space and the source value spaces lie in Lean's universe `Type`; reason: the source fixes no universe; every measurable space used in the mathematics is represented
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272, proof of Theorem 3.2, p. 12, display before "This holds for every binary coordination profile".

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model

namespace EntropyLocalCoord.Leader

/-- Proof of Theorem 3.2, p. 12: for every binary coordination profile `π`,
`I_leader(G, 𝔖) ≤ 2 h(½ C(G, π))`. -/
theorem ileader_le_entropy_cost {n k : ℕ} (G : SimpleGraph (Fin n))
    (S : InformationSkeleton n k) (π : CoordinationProfile S) (hπ : π.IsBinary) :
    Ileader G S ≤ 2 * h (1 / 2 * cost G π) := by sorry

end EntropyLocalCoord.Leader
