-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_residual_subcubic
-- name    : FasterExactColoring.ThreeColor.residual_subcubic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:48.805328+00:00
-- url     : https://prove2.me/theorems/7389bb14-f702-4337-83b8-a4f2bbc86e57
-- title:
--   Lemma 4.3 — residual subcubic graph
-- statement:
--   Let $G$ and $F$ satisfy the source's forest preprocessing conditions. Write $H=G-V(F)$, $S=N_G(R)\cap V(H)$, $T=V(H)\setminus S$, and $D=\{v\in S:\deg_H(v)=3\}$, where $R$ is the leaf set. Then
--   $$\Delta(H)\le3,\qquad \{v\in V(H):\deg_H(v)=3\}=D\cup T,$$
--   $$|\{v\in V(H):\deg_H(v)=3\}|=|D|+|T|,\qquad
--   v\in T\Longrightarrow\deg_H(v)=\deg_G(v)=3.$$
--   These are conclusions about the residual graph, not supplied assumptions. They identify the vertices counted by the later packing and width bounds.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: graph after the preprocessing of Section 4.2 → minimum degree three, acyclicity of ambient degree-three vertices, and a modified maximal bushy forest; valid internal roots and a maximal leaf matching where used; reason: these are exactly the source standing conditions, and counts are computed rather than assumed independent
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 4.3, p. 6 (PDF p. 8)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds

namespace FasterExactColoring.ThreeColor

theorem residual_subcubic (n : ℕ) (G : GraphInput n) (F : ForestData n)
  (h : forestPreprocessed G F) :
  (∀ v ∈ F.outside, degreeIn G F.outside v ≤ 3) ∧
  F.threeVertices G = F.D G ∪ F.T G ∧
  (F.threeVertices G).card = (F.D G).card + (F.T G).card ∧
  (∀ v ∈ F.T G, degreeIn G F.outside v = 3 ∧ degree G v = 3) := by sorry

end FasterExactColoring.ThreeColor
