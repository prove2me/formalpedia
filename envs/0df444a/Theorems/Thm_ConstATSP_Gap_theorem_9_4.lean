-- Prove2me | Theorems.Thm_ConstATSP_Gap_theorem_9_4
-- name    : ConstATSP.Gap.theorem_9_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:47:16.414226+00:00
-- url     : https://prove2.me/theorems/33cdf153-628f-48d7-ab5a-5d97cf6f5394
-- title:
--   Theorem 9.4, p. 46 — from vertebrate pairs to irreducible instances, ρ = (κ + η(1 − δ) + α_S + 3)/(2δ − 1)
-- statement:
--   Fix $\delta\in(1/2,1)$ and constants $\kappa,\eta\ge0$ and $\alpha_S$. Assume:
--
--   1. every singleton laminarly-weighted instance $I'$ with at least two vertices has a tour of weight at most $\alpha_S\,\mathrm{value}(I')$;
--   2. for every vertebrate pair $(I',B)$, with $I'$ a laminarly-weighted instance with at least two vertices, $I'$ has a tour of weight at most $\kappa\,\mathrm{value}(I')+\eta\,\mathrm{lb}_{I'}(\bar B)+w_{I'}(B)$.
--
--   Then every laminarly-weighted instance $I$ with at least two vertices that is irreducible with respect to $\delta$ has a tour $F$ with
--   $$w_I(F)\le\rho\,\mathrm{value}(I),\qquad \rho=\frac{\kappa+\eta(1-\delta)+\alpha_S+3}{2\delta-1}.$$
--
--   With $\kappa=2$, $\eta'=21$, $\alpha'_S=10$ and $\delta=0.78$ this gives $\rho'<35.04$ in §11 of the paper.
--
--   **Formalization Note** The paper states this result for a polynomial-time algorithm. Running times are not formalized: following §11 of the paper, which derives the integrality gap "non-constructively", the algorithm is read existentially, i.e. as the existence of the object the algorithm would return. Both assumed algorithms are posed as hypotheses quantified over instances on all finite vertex and edge types, because the paper applies them to instances it constructs. The page fixes $\alpha_S=18+\varepsilon$ through Corollary 5.2; here $\alpha_S$ is a parameter with hypothesis 1, as in §11. The instances are required to have at least two vertices.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 46, Theorem 9.4

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem theorem_9_4 (δ : ℝ) (hδ1 : 1 / 2 < δ) (hδ2 : δ < 1) (κ η αS : ℝ)
    (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (hAS : ∀ {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] (I' : Instance V' E'),
      I'.IsValid → I'.IsSingleton → ∃ F : E' → ℕ, IsTour I'.G F ∧ I'.wt F ≤ αS * I'.value)
    (hA : ∀ {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] (I' : Instance V' E'),
      I'.IsValid → ∀ B : E' → ℕ, I'.IsVertebrate B →
        ∃ F : E' → ℕ, IsTour I'.G F ∧ I'.wt F ≤ κ * I'.value + η * I'.lbCompl B + I'.wt B)
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : Instance V E) (hI : I.IsValid) (hirr : I.IsIrreducible δ) :
    ∃ F : E → ℕ, IsTour I.G F ∧
      I.wt F ≤ (κ + η * (1 - δ) + αS + 3) / (2 * δ - 1) * I.value := by sorry

end ConstATSP.Gap
