-- Prove2me | Theorems.Thm_ExitSpirals_proposition_2
-- name    : ExitSpirals.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:29.066991+00:00
-- url     : https://prove2.me/theorems/8c26c2bd-2633-4486-8819-1a20c0978bc3
-- title:
--   Proposition 2 — the maximal equilibrium is the largest mutually stable set of the stripped networks
-- statement:
--   Let $E_R,E_C$ be loopless directed networks on $n$ agents and $W$ a set of shocked agents. Let $y^*$ be the union of all equilibria of the best response (4). Then
--
--   1. $y^*$ is itself an equilibrium (so it is the maximal equilibrium);
--   2. $y^*$ is mutually stable in the stripped networks $(E_R(W),E_C(W))$, and every mutually stable subset of $(E_R(W),E_C(W))$ is contained in $y^*$.
--
--   In other words, the set of active agents in the maximal equilibrium conditional on $W$ equals the maximal mutually stable subset of $(G_R(W),G_C(W))$. This turns the equilibrium of the game into a purely graph-theoretic object.
--
--   **Formalization Note** Networks are `Finset`s of links on `Fin n`; the maximal equilibrium is `maxEq`, defined as the union of the fixed points of `bestResponse`.
--
--   Differences from the source:
--   - encoding: the maximal equilibrium of the game of §4.1 conditional on W → the union of all fixed points of the best response (4), with W given; reason: conditional on W the page's best response is (4) (p.22); the first conjunct states that the union is an equilibrium, i.e. that the maximal equilibrium exists
--   - encoding: agents N = {1, …, n}; a network as a set of directed links, i → j supporting j → agents Fin n; a network is a Finset of pairs, (j, i) ∈ E meaning j → i; reason: same objects; a Finset has no multiple links, as A.3 conditions on simple graphs
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Proposition 2, p.24

import Mathlib
import Definitions.Def_ExitSpirals_Network
import Definitions.Def_ExitSpirals_IsMutuallyStable
import Definitions.Def_ExitSpirals_activity

namespace ExitSpirals

/-- **Proposition 2 (maximal equilibrium and mutually stable subsets).**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Proposition 2,
p.24: "In the maximal equilibrium action profile conditional on the set W, denoted by y*, the set
of active agents (those with y*_i = 1) equals the maximal mutually stable subset of
(G_R(W), G_C(W))."

For loopless networks `ER`, `EC` on `Fin n` and any shocked set `W`, the union `maxEq ER EC W` of
the active sets of all equilibria of the best response (4) is itself an equilibrium, and it is
the greatest (under inclusion) mutually stable subset of the stripped networks
`(strip ER W, strip EC W)`.

**Formalization Note.** Agents are `Fin n`, networks are `Finset`s of links `(j, i)` = `j → i`.
The best response (4) is the primitive (see `bestResponse`). The first conjunct gives the
existence of the maximal equilibrium, which the page takes from supermodularity. -/
theorem proposition_2 {n : ℕ} (ER EC : Network n) (hR : IsLoopless ER) (hC : IsLoopless EC)
    (W : Finset (Fin n)) :
    IsEquilibrium ER EC W (maxEq ER EC W) ∧
      IsGreatest {V : Finset (Fin n) | IsMutuallyStable (strip ER W) (strip EC W) V}
        (maxEq ER EC W) := by sorry

end ExitSpirals
