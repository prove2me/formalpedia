-- Prove2me | Theorems.Thm_FMMM_TSM_tight_flow_is_max
-- name    : FMMM.TSM.tight_flow_is_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:31:20.365298+00:00
-- url     : https://prove2.me/theorems/f5d9deab-a139-414f-8f3e-9f80d4cb2cec
-- title:
--   §4.2.5, p. 10: the $6$-cycle flow is a maximum flow of the tight family
-- statement:
--   In the tight family with parameter $m \ge 1$ ($n = 4m$), the edges of the $m$ six-cycles $u_i - x_i - v_i - y_i - w_i - z_i - u_i$ form a maximum integral flow of the boosted flow graph $G_f$ (a maximum 2-matching of the edge set), of size $6m = 3n/2$. Every vertex of $U, V, W, X, Y, Z$ has flow $2$ and every vertex of $K$ and $L$ has flow $0$. The reachability cut obtained from this flow has source side $S = K \cup X \cup U \cup V \cup \{s\}$: the ads on the source side are $K \cup U \cup V$ and the impression types on the source side are $X$ (the surgery moves nothing). The cut also has size $3n/2$.
--
--   Differences from the source:
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the reachability cut (S, T) with S = K ∪ X ∪ U ∪ V ∪ {s} → residReach holds exactly on the ads with tag ≠ 3 (K, U, V) and the types with tag 1 (X); cutAds = K ∪ U ∪ V and the surgered cutImps = X; cut value 2(|A_T| + |I_S|) + |E_δ| = 6m; reason: the source vertex is implicit; the cut is given by its ads and impressions; the encoding of the family by Fin 4 × Fin m
--   - encoding: i ∈ [1, n/4] → Fin m, 0-based, with m ≥ 1 and n = 4m; reason: same family
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.5, p. 10 (max-flow and min-cut of the tight family)

import Mathlib
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_tightFlow
import Definitions.Def_FMMM_TSM_tightE
import Definitions.Def_FMMM_TSM_cutAds
import Definitions.Def_FMMM_TSM_residReach
import Definitions.Def_FMMM_TSM_cutImps
import Definitions.Def_FMMM_TSM_eDelta

namespace FMMM.TSM

/-- **The 6-cycle flow of the tight family is a maximum flow; its reachability cut.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.5, p. 10: "We now describe the max-flow and min-cut in G_f found during the algorithm. The
only edges with (unit) flow are the edges of the 6-cycles, i.e., for i ∈ [1, n/4],
{u_i − x_i − v_i − y_i − w_i − z_i − u_i}. Thus all vertices in U, V, W, X, Y and Z have a flow of 2
each, and the vertices in K and L have a flow of 0. The reachability cut (S, T) obtained from this
flow has S = K ∪ X ∪ U ∪ V ∪ {s} (where s is the source vertex). The flow and the cut both have size
3n/2."

For `m ≥ 1` (`n = 4m`): `tightFlow m` is a maximum 2-matching of `tightE m` with `6m = 3n/2` edges;
every vertex of `U, V, W` and of `X, Y, Z` carries flow 2 and every vertex of `K` and `L` flow 0;
the vertices reachable from `s` in the residual graph are exactly the ads `K ∪ U ∪ V` (tags 0, 1, 2)
and the impressions `X` (tag 1); the surgery moves nothing, so the cut `(S, T)` has `A_S = K ∪ U ∪ V`
and `I_S = X`; and the cut has value `2(|A_T| + |I_S|) + |E_δ| = 6m = 3n/2`. -/
theorem tight_flow_is_max (m : ℕ) (hm : 1 ≤ m) :
    IsMaxTwoMatching (tightE m) (tightFlow m) ∧ (tightFlow m).card = 6 * m ∧
    (∀ a : Fin 4 × Fin m,
      ((tightFlow m).filter (fun e => e.1 = a)).card = if a.1 = 0 then 0 else 2) ∧
    (∀ j : Fin 4 × Fin m,
      ((tightFlow m).filter (fun e => e.2 = j)).card = if j.1 = 0 then 0 else 2) ∧
    cutAds (tightE m) (tightFlow m) = Finset.univ.filter (fun a => a.1 ≠ 3) ∧
    (∀ v : (Fin 4 × Fin m) ⊕ (Fin 4 × Fin m), residReach (tightE m) (tightFlow m) v ↔
      Sum.elim (fun a => a.1 ≠ 3) (fun j => j.1 = 1) v) ∧
    cutImps (tightE m) (tightFlow m) = Finset.univ.filter (fun j => j.1 = 1) ∧
    2 * ((Finset.univ \ cutAds (tightE m) (tightFlow m)).card +
        (cutImps (tightE m) (tightFlow m)).card) + (eDelta (tightE m) (tightFlow m)).card = 6 * m := by sorry

end FMMM.TSM
