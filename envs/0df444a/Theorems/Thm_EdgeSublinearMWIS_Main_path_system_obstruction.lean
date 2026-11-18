-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_path_system_obstruction
-- name    : EdgeSublinearMWIS.Main.path_system_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T18:05:56.537035+00:00
-- url     : https://prove2.me/theorems/ef236adb-ae71-4b82-b5ff-391c91e09316
-- title:
--   Lemma 11 — short induced path systems are obstructed
-- statement:
--   Let $\mathcal C$ be hereditary, let $a\ge2$ be an integer, and suppose a fixed $K>0$ gives
--   $$\operatorname{tw}(G)\le K|E(G)|^{1-1/a}\qquad(G\in\mathcal C).$$
--   There is a constant $D>0$, fixed for the class and its treewidth bound, such that for every real $\ell\ge1$ one can choose a finite subcubic graph $H$, with at least one edge, satisfying
--   $$|V(H)|\le D\ell^{2a-2},$$
--   for which every induced almost-embedding $(\phi,\pi)$ into every graph $G\in\mathcal C$ satisfies
--   $$\sum_{e\in E(H)}|V(\pi(e))|>4\ell|E(H)|.$$
--   The graph $H$ is chosen before the host graph. This is the structural obstruction underlying Lemma 11: it separates the path-system and treewidth argument from the finite sampling argument.
-- source:
--   Édouard Bonnet and Yeonsu Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, STOC 2027 submission #1044 (October 2026), proof of Lemma 11, p.11, Eqs. (11)–(12) and final treewidth contradiction, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Paths

open scoped BigOperators Classical

namespace EdgeSublinearMWIS.Main

theorem path_system_obstruction (C : GraphClass) (a : ℕ) (K : ℝ)
    (hereditary : Hereditary C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    ∃ D : ℝ,0 < D ∧ ∀ ell : ℝ,1 ≤ ell →
      ∃ (h : ℕ) (H : SimpleGraph (Fin h)),0 < Fintype.card (EdgeIndex H) ∧
        (h:ℝ) ≤ D*ell^(2*a-2) ∧ (∀ v,degree H v ≤ 3) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),C n G →
          ∀ E : AlmostEmbedding H G,E.Induced →
            4*ell*Fintype.card (EdgeIndex H) < (∑ e : EdgeIndex H,((E.path e).length:ℝ)) := by sorry

end EdgeSublinearMWIS.Main
