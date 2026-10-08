-- Prove2me | Theorems.Thm_AssocRealizations_SantosFan_lemma_5_3
-- name    : AssocRealizations.SantosFan.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:52.934268+00:00
-- url     : https://prove2.me/theorems/9afcd8d8-f57e-4bbd-886a-67427f77585a
-- title:
--   Lemma 5.3 — a flip gives a linear dependence with nonzero coefficients of equal sign on the flipped diagonals
-- statement:
--   Let $T_0$ be a triangulation of the convex $(n+3)$-gon, with Santos' vectors $v_e \in \mathbb R^{T_0}$. Let $T_1$ and $T_2$ be triangulations that differ by a flip: $T_1 \setminus T_2 = \{v_1\}$ and $T_2 \setminus T_1 = \{v_2\}$. Then there are coefficients $\lambda_e$ with
--   $$\sum_{e \in T_1 \cup T_2} \lambda_e\, v_e = 0, \qquad \lambda_{v_1} > 0, \qquad \lambda_{v_2} > 0.$$
--
--   That is, the vectors of $T_1 \cup T_2$ have a linear dependence whose coefficients at the removed and the inserted diagonal have the same sign and are nonzero. This is assertion (2) of §5.1: it says that adjacent cones $\mathbb R_{\ge0}T_1$ and $\mathbb R_{\ge0}T_2$ lie on opposite sides of their common facet.
--
--   **Formalization Note** The printed Lemma 5.3 says "coefficients of the same sign"; assertion (2), of which it is the proof, adds "(and different from zero)". Without nonvanishing the zero dependence would satisfy the statement, so both coefficients are required to be strictly positive (a dependence with both negative is turned into this one by multiplying by $-1$).
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 20, Lemma 5.3 and §5.1 assertion (2)

import Mathlib
import Definitions.Def_AssocRealizations_SantosFan_Setting

namespace AssocRealizations.SantosFan

open ChvatalArtGallery.FanPartition

/-- Lemma 5.3 with assertion (2) of §5.1 (p. 20): if the triangulations `T₁` and `T₂` differ by
a flip removing `v₁` and inserting `v₂`, there is a linear dependence among the vectors of
`T₁ ∪ T₂` whose coefficients at `v₁` and `v₂` have the same sign and are nonzero (normalized to
be positive). -/
theorem lemma_5_3 (n : ℕ) (T₀ T₁ T₂ : Finset (Sym2 (Fin (n + 3)))) (v₁ v₂ : Sym2 (Fin (n + 3)))
    (h₀ : IsTriangulation (n + 3) T₀) (h₁ : IsTriangulation (n + 3) T₁)
    (h₂ : IsTriangulation (n + 3) T₂) (h₁₂ : T₁ \ T₂ = {v₁}) (h₂₁ : T₂ \ T₁ = {v₂}) :
    ∃ c : Sym2 (Fin (n + 3)) → ℝ,
      ∑ e ∈ T₁ ∪ T₂, c e • AssocRealizations.TypesMeet.santosVec T₀ e = 0 ∧ 0 < c v₁ ∧ 0 < c v₂ := by sorry

end AssocRealizations.SantosFan
