-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_treewidth_separator
-- name    : EdgeSublinearMWIS.Main.treewidth_separator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:38:33.606213+00:00
-- url     : https://prove2.me/theorems/9099e9b1-b481-47d2-9182-974e8841f836
-- title:
--   Balanced separators from a tree decomposition
-- statement:
--   Let $G$ be a finite simple graph and let $W\subseteq V(G)$. There is a set $S\subseteq W$ such that every connected component of $G[W\setminus S]$ has at most $2|W|/3$ vertices and
--   $$|S|\le\operatorname{tw}(G)+1.$$
--   This is the decomposition-to-separator implication used in Theorem 5 and at the end of Lemma 16. The statement also includes empty and singleton vertex sets.
-- source:
--   Bonnet and Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, STOC 2027 submission #1044, p.5 Theorem 5 (decomposition-to-separator implication) and p.20, final sentence of the proof of Lemma 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs

namespace EdgeSublinearMWIS.Main

theorem treewidth_separator {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) :
    ∃ S : Finset (Fin n), Balanced G W S ∧ S.card ≤ PlantedSubgraphLD.tw G + 1 := by sorry

end EdgeSublinearMWIS.Main
