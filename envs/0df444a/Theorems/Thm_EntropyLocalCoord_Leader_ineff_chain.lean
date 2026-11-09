-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_ineff_chain
-- name    : EntropyLocalCoord.Leader.ineff_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:05.815195+00:00
-- url     : https://prove2.me/theorems/fb7f74c6-af3c-4c4f-9a3a-2e79078f48ed
-- title:
--   §2, p. 6 — a leader profile of cost at most 1 exists, and $I\le I_{\mathrm{bin}}\le I_{\mathrm{leader}}\le1$
-- statement:
--   Let $G=(N,E)$ be a finite simple graph and $\mathfrak S=(N,K,B)$ an information skeleton. There is a leader profile adapted to $\mathfrak S$ of cost at most $1$, and consequently
--
--   $$I(G,\mathfrak S)\le I_{\mathrm{bin}}(G,\mathfrak S)\le I_{\mathrm{leader}}(G,\mathfrak S)\le1.$$
--
--   Here $I$, $I_{\mathrm{bin}}$ and $I_{\mathrm{leader}}$ are the infima of the cost $C(G,\pi)$ over adapted, binary and leader profiles.
--
--   The first clause shows that all three classes of profiles are nonempty, so the three infima are genuine infima of nonempty sets.
--
--   Differences from the source:
--   - encoding: the players are $N=\{1,\dots,n\}$ and the sources $K=\{1,\dots,k\}$ → the types `Fin n` and `Fin k`, indexed from 0, with $n=0$ admitted by the type; reason: a relabeling; the empty-player instance adds only a trivial case and changes no source instance
--   - encoding: $C(G,\pi)$ divides by $|E|$, undefined for an edgeless graph → the Lean quotient, with value 0 when $|E|=0$; reason: this only fills a case the source leaves undefined; no hypothesis on $E$ is added
--   - encoding: an arbitrary probability space and arbitrary source variables → the sample space and the source value spaces lie in Lean's universe `Type`; reason: the source fixes no universe; every measurable space used in the mathematics is represented
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272, §2, p. 6, display after the definition of the inefficiencies.

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model

namespace EntropyLocalCoord.Leader

/-- §2, p. 6: a leader profile of cost at most `1` exists, and consequently
`I(G, 𝔖) ≤ I_bin(G, 𝔖) ≤ I_leader(G, 𝔖) ≤ 1`. -/
theorem ineff_chain {n k : ℕ} (G : SimpleGraph (Fin n)) (S : InformationSkeleton n k) :
    (∃ π : CoordinationProfile S, π.IsLeader ∧ cost G π ≤ 1) ∧
      Ineff G S ≤ Ibin G S ∧ Ibin G S ≤ Ileader G S ∧ Ileader G S ≤ 1 := by sorry

end EntropyLocalCoord.Leader
