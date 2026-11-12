-- Prove2me | Theorems.Thm_BunkbedTM_profile_indicator
-- name    : BunkbedTM.profile_indicator
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T15:59:44.968875+00:00
-- url     : https://prove2.me/theorems/e8a907a3-9f23-464d-9835-b8a829870156
-- title:
--   Bunkbed connectivity on Hollom's hypergraph depends only on the two level profiles
-- statement:
--   In the Wierman--Ziff five-state model on Hollom's $3$-uniform hypergraph, the difference between the cross-level and the same-level connection probability is a sum over the $5^{12}$ pairs of level configurations. This statement performs the two reductions that make that sum finite to work with.
--
--   First, the two levels are conditionally independent: each hyperedge draws its state independently on each level, and the posts over the transversal set $T = \{1, 6, 8\}$ are always present. So the sum factors into a double sum over a level-$0$ configuration $c_0$ and a level-$1$ configuration $c_1$, weighted by $\prod_i P(c_0(i)) \cdot \prod_i P(c_1(i))$.
--
--   Second — and this is the combinatorial heart — whether vertex $0$ on level $0$ is connected to vertex $9$ on level $l$ depends on $c_0$ and $c_1$ **only through the partitions they induce on the five special vertices** $\{0, 1, 6, 8, 9\}$: the two endpoints of the connection event together with the transversal set. Nothing else about the configuration matters, because a walk can change level only at a post, and the posts stand over $T$, which is part of the recorded boundary. Writing `prof` for that induced partition and `glueConn` for the resulting glued connectivity, the indicator of the connection event is exactly $\texttt{glueConn}(\texttt{prof}\,c_0, \texttt{prof}\,c_1, l)$.
-- source:
--   Gladkov, Pak, Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) no. 24, e2420725122; Section 3, Lemma 3.3 and Hollom's 3-uniform hypergraph (Fig. 1), with the path $\rho$ of Eq. [5].

import Definitions.Def_BunkbedTransferTables
open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

theorem BunkbedTM.profile_indicator (P : WZ → ℚ) :
    wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2))
      - wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))
      = ∑ c₀ : Fin 6 → WZ, ∑ c₁ : Fin 6 → WZ,
          ((if glueConn (prof c₀) (prof c₁) 1 then (1 : ℚ) else 0)
            - (if glueConn (prof c₀) (prof c₁) 0 then (1 : ℚ) else 0))
            * ((∏ i, P (c₀ i)) * (∏ i, P (c₁ i))) := by sorry
