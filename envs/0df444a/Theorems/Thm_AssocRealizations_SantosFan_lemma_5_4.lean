-- Prove2me | Theorems.Thm_AssocRealizations_SantosFan_lemma_5_4
-- name    : AssocRealizations.SantosFan.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:22.585435+00:00
-- url     : https://prove2.me/theorems/a70ab92e-4244-4e69-abbf-a8a4103086bb
-- title:
--   Lemma 5.4 — a complete simplicial fan is a normal fan iff it admits positive weights making every flip dependence positive
-- statement:
--   Let $N \ge 0$ and let $(v_e)$ be vectors in $\mathbb R^\iota$ ($\iota$ finite), one for each chord $e$ of the convex $N$-gon, such that the cones $\mathbb R_{\ge0}T$ of the triangulations $T$ form a complete simplicial fan (the vectors of each triangulation are linearly independent, the cones cover $\mathbb R^\iota$, and two of them meet in the cone of their common diagonals). Let $\mathcal F$ be the fan of all cones $\mathbb R_{\ge0}D$, $D$ a set of pairwise non-crossing diagonals. The following are equivalent:
--   1. $\mathcal F$ is the normal fan of a polytope: there is a polytope $P$ with $\mathcal F = \{N_P(x) : x \in P\}$, $N_P(x)$ the exterior normal cone;
--   2. there is $\omega$ with $\omega_e > 0$ for every diagonal $e$ such that, for every pair of triangulations with $T_1 \setminus T_2 = \{v_1\}$ and $T_2 \setminus T_1 = \{v_2\}$, every $\lambda$ with
--   $$\sum_{e \in T_1 \cup T_2} \lambda_e v_e = 0, \quad \lambda_{v_1} > 0, \quad \lambda_{v_2} > 0 \qquad\text{satisfies}\qquad \sum_{e \in T_1\cup T_2} \lambda_e \omega_e > 0.$$
--
--   This turns polytopality of a complete simplicial fan into the feasibility of a finite system of strict linear inequalities in $\omega$.
--
--   **Formalization Note** The paper states the lemma for an arbitrary complete simplicial fan with generator set $A$. Here the fan is one whose rays are indexed by the diagonals of a polygon and whose maximal cones are the triangulations, which is the case the paper applies it to. Pairs of adjacent maximal cones are pairs of triangulations sharing all but one diagonal. The paper uses "the" dependence with support in $C_1 \cup C_2$ (unique up to scaling); the statement quantifies over every dependence positive at $v_1$ and $v_2$, which is the same condition when the dependence is unique. The paper proves (2) ⇒ (1) and cites [8, Cor. 9.5.3] for the equivalence; the full equivalence is stated.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 22, Lemma 5.4

import Mathlib
import Definitions.Def_AssocRealizations_SantosFan_Setting

namespace AssocRealizations.SantosFan

open ChvatalArtGallery.FanPartition

/-- Lemma 5.4 (p. 22), for fans whose rays are indexed by the diagonals of the `N`-gon and whose
maximal cones are the triangulations: if these cones form a complete simplicial fan, then the fan
is the normal fan of a polytope if and only if there is a weight `ω > 0` on the generators such
that every linear dependence of two adjacent maximal cones, positive on the two flipped
diagonals, has positive `ω`-weight. -/
theorem lemma_5_4 {N : ℕ} {ι : Type*} [Fintype ι] (v : Sym2 (Fin N) → (ι → ℝ))
    (hF : IsCompleteSimplicialFan v) :
    (∃ P : Set (ι → ℝ), IsNormalFanOf (AssocRealizations.TypesMeet.rayFan v) P) ↔
      ∃ ω : Sym2 (Fin N) → ℝ, WeightCondition v ω := by sorry

end AssocRealizations.SantosFan
