-- Prove2me | Theorems.Thm_ExitSpirals_lemma_2
-- name    : ExitSpirals.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:25.813049+00:00
-- url     : https://prove2.me/theorems/4362dce0-42bc-4a60-a277-0bb264144811
-- title:
--   Lemma 2 — with an in-link in both networks everywhere and no shock, every agent is active
-- statement:
--   Let $E_R,E_C$ be loopless directed networks on $n$ agents in which every agent has at least one incoming link in $E_R$ and at least one in $E_C$ (Assumption 4.3). With no shocked agent ($x=1$, $W=\emptyset$),
--   $$y^*=N,$$
--   i.e. all agents are active in the maximal equilibrium, and the set of all agents is mutually stable.
--
--   This is the pre-shock baseline from which the post-shock regime is studied.
--
--   Differences from the source:
--   - encoding: x = 1 ('at x = 1', Assumption 4.3) → the shocked set W = ∅; reason: at x = 1 no agent is shocked
--   - encoding: agents N = {1, …, n}; a network as a set of directed links, i → j supporting j → agents Fin n; a network is a Finset of pairs, (j, i) ∈ E meaning j → i; reason: same objects; a Finset has no multiple links, as A.3 conditions on simple graphs
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Lemma 2, p.48; Assumption 4.3, p.23

import Mathlib
import Definitions.Def_ExitSpirals_Network
import Definitions.Def_ExitSpirals_IsMutuallyStable
import Definitions.Def_ExitSpirals_activity

namespace ExitSpirals

/-- **Lemma 2 (with an in-link everywhere, everyone is active).**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Lemma 2, p.48:
"Suppose Assumption 4.3 is satisfied. Then in a maximal equilibrium, y*_i = 1 for all i;
equivalently, the maximal stable set consists of all nodes." Assumption 4.3, p.23: "All agents
have at least one incoming edge in G_R and G_C", stated for x = 1, i.e. no agent is shocked.

For loopless networks in which every agent has positive in-degree in both, the maximal
equilibrium with no shocked agent (`W = ∅`) is the set of all agents, and the set of all agents
is mutually stable.

**Formalization Note.** "x = 1" is encoded as the empty shocked set `W = ∅`. -/
theorem lemma_2 {n : ℕ} (ER EC : Network n) (hR : IsLoopless ER) (hC : IsLoopless EC)
    (h43R : ∀ i, 0 < inDeg ER i) (h43C : ∀ i, 0 < inDeg EC i) :
    maxEq ER EC ∅ = Finset.univ ∧ IsMutuallyStable ER EC Finset.univ := by sorry

end ExitSpirals
