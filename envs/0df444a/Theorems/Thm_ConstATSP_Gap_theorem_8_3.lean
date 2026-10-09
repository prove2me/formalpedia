-- Prove2me | Theorems.Thm_ConstATSP_Gap_theorem_8_3
-- name    : ConstATSP.Gap.theorem_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:47:19.403733+00:00
-- url     : https://prove2.me/theorems/5667e650-5d62-459c-b342-bce9942d734e
-- title:
--   Theorem 8.3, p. 42 — from irreducible to general laminarly-weighted instances, factor 2ρ/(1 − δ)
-- statement:
--   Fix $\delta\in(1/2,1)$ and a constant $\rho$. Assume that every laminarly-weighted ATSP instance $I'$ with at least two vertices that is irreducible with respect to $\delta$ has a tour of weight at most $\rho\,\mathrm{value}(I')$. Then every laminarly-weighted instance $I$ with at least two vertices has a tour $F$ with
--   $$w_I(F)\le\frac{2\rho}{1-\delta}\,\mathrm{value}(I).$$
--
--   Here $\mathrm{value}(I)$ is the Held–Karp lower bound of the instance (Def. 2.6). With $\rho'<35.04$ and $\delta=0.78$ the factor is at most $319$, the final bound of §11.
--
--   **Formalization Note** The paper states this result for a polynomial-time algorithm. Running times are not formalized: following §11 of the paper, which derives the integrality gap "non-constructively", the algorithm is read existentially, i.e. as the existence of the object the algorithm would return. The assumed algorithm is posed as a hypothesis quantified over instances on all finite vertex and edge types, because the paper applies it to instances obtained by contraction and induction. The instances are required to have at least two vertices.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 42, Theorem 8.3

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem theorem_8_3 (δ : ℝ) (hδ1 : 1 / 2 < δ) (hδ2 : δ < 1) (ρ : ℝ)
    (hA : ∀ {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] (I' : Instance V' E'),
      I'.IsValid → I'.IsIrreducible δ → ∃ F : E' → ℕ, IsTour I'.G F ∧ I'.wt F ≤ ρ * I'.value)
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : Instance V E) (hI : I.IsValid) :
    ∃ F : E → ℕ, IsTour I.G F ∧ I.wt F ≤ 2 * ρ / (1 - δ) * I.value := by sorry

end ConstATSP.Gap
