-- Prove2me | Theorems.Thm_AssocRealizations_SantosFan_weights_condition
-- name    : AssocRealizations.SantosFan.weights_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:45.198153+00:00
-- url     : https://prove2.me/theorems/60256901-1303-4183-81eb-58017f447c90
-- title:
--   pp. 22–23 — the weights $\omega_{ij}=2$ on $T_0$, $1+\varepsilon g_{ij}$ off $T_0$ satisfy condition (2) of Lemma 5.4 for small $\varepsilon$
-- statement:
--   Let $T_0$ be a triangulation of the convex $(n+3)$-gon with Santos' vectors $v_e \in \mathbb R^{T_0}$. For $\varepsilon \in \mathbb R$ define the weights
--   $$\omega_{ij} = \begin{cases} 2, & ij \in T_0,\\ 1 + \varepsilon\, g_{ij}, & ij \notin T_0,\end{cases} \qquad g_{ij} = (j - i)(n + 3 + i - j).$$
--   Then there is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon < \varepsilon_0$ the weights $\omega$ satisfy condition (2) of Lemma 5.4: $\omega_e > 0$ on every diagonal, and for every pair of triangulations $T_1, T_2$ with $T_1 \setminus T_2 = \{v_1\}$, $T_2 \setminus T_1 = \{v_2\}$ and every $\lambda$ with $\sum_{e \in T_1\cup T_2} \lambda_e v_e = 0$, $\lambda_{v_1}>0$, $\lambda_{v_2} > 0$,
--   $$\sum_{e \in T_1 \cup T_2} \omega_e \lambda_e > 0.$$
--
--   With Theorem 5.1 and Lemma 5.4 this gives Theorem 5.2.
--
--   **Formalization Note** Positions of the polygon are $0, \dots, n+2$; on a chord with positions $a < b$ the weight uses $g = (b-a)(n+3+a-b)$, which is the paper's $g_{ij}$ with the vertices numbered $1, \dots, n+3$. The page checks the weights on "the linear dependences exhibited in equations (4)–(7)"; these are the dependences of all flip pairs, each unique up to a positive factor, so the statement quantifies over all flip pairs and all such dependences. "Sufficiently small $\varepsilon$" is the quantifier $\exists \varepsilon_0 > 0\ \forall \varepsilon \in (0, \varepsilon_0)$.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, pp. 22–23, proof of Theorem 5.2 (last paragraph of p. 22 and p. 23)

import Mathlib
import Definitions.Def_AssocRealizations_SantosFan_Setting

namespace AssocRealizations.SantosFan

open ChvatalArtGallery.FanPartition

/-- pp. 22–23: for every seed triangulation `T₀` there is `ε₀ > 0` such that, for every
`0 < ε < ε₀`, the weights `ω_ij = 2` (`ij ∈ T₀`) and `ω_ij = 1 + ε g_ij` (`ij ∉ T₀`) satisfy
condition (2) of Lemma 5.4 for Santos' vectors. -/
theorem weights_condition (n : ℕ) (T₀ : Finset (Sym2 (Fin (n + 3))))
    (h₀ : IsTriangulation (n + 3) T₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      WeightCondition (AssocRealizations.TypesMeet.santosVec T₀) (santosWeight T₀ ε) := by sorry

end AssocRealizations.SantosFan
