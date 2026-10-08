-- Prove2me | Theorems.Thm_AssocRealizations_SantosFan_seed_cone_unique
-- name    : AssocRealizations.SantosFan.seed_cone_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:29.642038+00:00
-- url     : https://prove2.me/theorems/a0a2f1e8-2e05-4230-aae0-5974f86f2f4c
-- title:
--   §5.1, assertion (1) — the seed cone is the negative orthant and the only cone meeting its interior
-- statement:
--   Let $T_0$ be a triangulation of the convex $(n+3)$-gon, with Santos' vectors $v_{pq} \in V = \mathbb R^{T_0}$ and fan $\mathcal F_{T_0}$ (the cones $\mathbb R_{\ge0}D$ of all sets $D$ of pairwise non-crossing diagonals). Then:
--   1. the vectors $v_\delta = -\alpha_\delta$, $\delta \in T_0$, are linearly independent, so $\mathbb R_{\ge 0}T_0$ is a simplicial cone;
--   2. $\mathbb R_{\ge0}T_0$ is the closed negative orthant $\{x \in V : x_\delta \le 0 \text{ for all } \delta\}$;
--   3. it is the only cone $C \in \mathcal F_{T_0}$ that contains a point of the open negative orthant:
--   $$C \in \mathcal F_{T_0},\ \exists x \in C \text{ with } x_\delta < 0 \ \forall \delta \in T_0 \implies C = \mathbb R_{\ge 0} T_0.$$
--
--   Together with Lemma 5.3, this is one of the two facts from which the paper derives Theorem 5.1: some part of $V$ is covered by exactly one cone.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 20, §5.1, assertion (1); p. 19 for R≥0T0 being the negative orthant

import Mathlib
import Definitions.Def_AssocRealizations_SantosFan_Setting

namespace AssocRealizations.SantosFan

open ChvatalArtGallery.FanPartition

/-- §5.1, assertion (1) (p. 20): `ℝ≥0 T₀` is a simplicial cone, it is the closed negative
orthant, and it is the only cone of `𝓕_{T₀}` that meets the interior of the negative orthant. -/
theorem seed_cone_unique (n : ℕ) (T₀ : Finset (Sym2 (Fin (n + 3))))
    (h₀ : IsTriangulation (n + 3) T₀) :
    LinearIndependent ℝ (fun e : {e // e ∈ T₀} => AssocRealizations.TypesMeet.santosVec T₀ e.1) ∧
    maxCone T₀ T₀ = {x | ∀ d, x d ≤ 0} ∧
    ∀ C ∈ AssocRealizations.TypesMeet.santosFan T₀, (∃ x ∈ C, ∀ d, x d < 0) → C = maxCone T₀ T₀ := by sorry

end AssocRealizations.SantosFan
