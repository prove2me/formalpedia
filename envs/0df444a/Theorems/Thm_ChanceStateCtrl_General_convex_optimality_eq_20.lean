-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_convex_optimality_eq_20
-- name    : ChanceStateCtrl.General.convex_optimality_eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:40.801173+00:00
-- url     : https://prove2.me/theorems/09a9991a-4f87-40e0-8aa1-11b06248e110
-- title:
--   Proof of Proposition 2.6, p. 8 (citing [39, Thm 3.66]) — KKT characterization for (20) with an extended-valued convex constraint
-- statement:
--   Let $U$ be a real Banach space, $F:U\to\mathbb R$ convex and Fréchet differentiable, and $f:U\to\mathbb R\cup\{+\infty\}$ convex and lower semicontinuous. Assume a Slater point exists, $f(\hat u)<0$ for some $\hat u$, and let $u^*$ be feasible, $f(u^*)\le0$, with $f$ finite and continuous on a neighbourhood of $u^*$. Then $u^*$ is a solution of
--   $$
--   \min_{u\in U}\{F(u)\mid f(u)\le0\}
--   $$
--   if and only if there is $\lambda\ge0$ with
--   $$
--   -DF(u^*)\in\lambda\,\partial f(u^*),\qquad\lambda f(u^*)=0,
--   $$
--   where $\partial$ is the subdifferential of convex analysis.
--
--   Applied to $f=\tilde\varphi$, this is the step of the proof of Proposition 2.6 that characterizes the solutions of the convex reformulation (20).
--
--   **Formalization Note** The paper invokes this as "classical convex analysis (admitting extended-valued inequality constraints, e.g., [39, Theorem 3.66, Remark 3.67])" without spelling out the hypotheses. The finiteness and continuity of $f$ near $u^*$ is an added, disclosed hypothesis: it is the standard sufficient constraint qualification together with the Slater point, it guarantees $\partial f(u^*)\neq\emptyset$ (so the case $\lambda=0$ reads $DF(u^*)=0$), and in the application it holds because $\varphi$ is locally Lipschitzian and positive near $u^*$. "$-DF(u^*)\in\lambda\partial f(u^*)$" is written as "there is $x^*\in\partial f(u^*)$ with $-DF(u^*)=\lambda x^*$".
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 8, proof of Proposition 2.6; stated in this paper, citing [39, Theorem 3.66, Remark 3.67]

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem convex_optimality_eq_20 {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [CompleteSpace U] (F : U → ℝ) (hF_convex : ConvexOn ℝ Set.univ F)
    (hF_diff : Differentiable ℝ F) (f : U → EReal) (hf_convex : ConvexEpi f)
    (hf_ne_bot : ∀ u, f u ≠ ⊥) (hf_lsc : LowerSemicontinuous f)
    (hslater : ∃ uh : U, f uh < 0) (us : U) (hus : f us ≤ 0)
    (hf_cont : ∃ t ∈ 𝓝 us, (∀ u ∈ t, f u ≠ ⊤) ∧ ContinuousOn (fun u => (f u).toReal) t) :
    IsSolution {u | f u ≤ 0} F us ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ (∃ x ∈ convexSubdiffE f us, -(fderiv ℝ F us) = lam • x) ∧
        lam * (f us).toReal = 0 := by sorry

end ChanceStateCtrl.General
