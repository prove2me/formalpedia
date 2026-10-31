-- Prove2me | Theorems.Thm_CombOpt_TJoin_cut_parity
-- name    : CombOpt.TJoin.cut_parity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:50.021983+00:00
-- url     : https://prove2.me/theorems/a01b0064-cc16-463d-9dc8-31c62df7b9e6
-- title:
--   Parity of a $T$-join on a cut: $|J\cap\delta(S)|\equiv|S\cap T|\pmod 2$
-- statement:
--   Let $G=(V,E)$ be a graph, $T\subseteq V$ with $|T|$ even, and $J$ a $T$-join of $G$. Then for every $S\subseteq V$,
--
--   $$|J\cap\delta(S)|\equiv|S\cap T|\pmod 2.$$
--
--   In particular a $T$-join meets every $T$-cut in an odd number of edges, which gives the valid inequalities of the linear programs (5.33) and (5.37).
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, p. 180 (PDF p. 188)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin

namespace CombOpt.TJoin

open scoped symmDiff

/-- **Parity of a T-join on a cut.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 180 (PDF p. 188): "Let J be a T-join and let S be a subset of V. Then
|J ∩ δ(S)| ≡ |S ∩ T| (mod 2)." -/
theorem cut_parity {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (hT : Even T.card) (J : Finset E) (hJ : G.IsTJoin T J)
    (S : Finset V) :
    (J ∩ G.cut S).card ≡ (S ∩ T).card [MOD 2] := by sorry

end CombOpt.TJoin
