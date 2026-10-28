-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_convex_subdiff_eq_clarke
-- name    : ChanceStateCtrl.General.convex_subdiff_eq_clarke
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:45.629154+00:00
-- url     : https://prove2.me/theorems/9bc89d69-e250-4d86-a51a-85af7de9523b
-- title:
--   Proof of Proposition 2.6, p. 8 (citing [10, Prop 2.2.7]) — for locally Lipschitz convex functions ∂f = ∂^C f
-- statement:
--   Let $U$ be a real normed space, $S\subseteq U$ open and convex, $f:U\to\mathbb R$ convex on $S$, and $u\in S$ a point around which $f$ is locally Lipschitzian. Then the subdifferential of convex analysis of $f$ on $S$ coincides with Clarke's subdifferential:
--   $$
--   \{x^*\in U^*\mid f(u)+\langle x^*,w-u\rangle\le f(w)\ \forall w\in S\}=\partial^Cf(u).
--   $$
--
--   In the proof of Proposition 2.6 this identifies $\partial\tilde\varphi(u^*)$ with $\partial^C\tilde\varphi(u^*)$, linking the convex optimality condition for (20) to Clarke's calculus.
--
--   **Formalization Note** The paper states this citing [10, Proposition 2.2.7], which is formulated for a function convex on an open convex set and Lipschitz near the point; it is stated here in that form. In the application $S$ is a convex neighbourhood of $u^*$ on which $\tilde\varphi$ is finite.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 8, proof of Proposition 2.6; stated in this paper, citing [10, Proposition 2.2.7]

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem convex_subdiff_eq_clarke {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (S : Set U) (hS_open : IsOpen S) (f : U → ℝ) (hf : ConvexOn ℝ S f) (u : U) (hu : u ∈ S)
    (hf_lip : LocLipAt f u) :
    {x : StrongDual ℝ U | ∀ w ∈ S, f u + x (w - u) ≤ f w} = clarkeSubdiff f u := by sorry

end ChanceStateCtrl.General
