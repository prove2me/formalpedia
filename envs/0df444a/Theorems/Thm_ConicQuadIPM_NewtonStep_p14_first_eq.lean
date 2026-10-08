-- Prove2me | Theorems.Thm_ConicQuadIPM_NewtonStep_p14_first_eq
-- name    : ConicQuadIPM.NewtonStep.p14_first_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:19.060982+00:00
-- url     : https://prove2.me/theorems/33731d23-5ca1-4431-8c0e-ac2ae74de1d6
-- title:
--   Proof of Lemma 4.1, p. 14, first equality — (x⁽⁰⁾)ᵀd_s + (s⁽⁰⁾)ᵀd_x = eᵀ(X⁽⁰⁾Td_s + S⁽⁰⁾Td_x)
-- statement:
--   Let $K = K^1\times\cdots\times K^k$ be a product of cones of the kinds $\mathbb R_+$, $K^q$, $K^r$ with the usual dimension conventions, $T = \operatorname{diag}(T^1,\dots,T^k)$ the matrix of Definition 3.2 and (22), and $e = (e^1;\dots;e^k)$ the stacked first unit vectors. For arbitrary vectors $x^{(0)}, s^{(0)}, d_x, d_s$ and reals $\tau^{(0)},\kappa^{(0)},d_\tau,d_\kappa$, with $X^{(0)} = \operatorname{diag}(\operatorname{mat}(T^ix^{(0)i}))$ and $S^{(0)} = \operatorname{diag}(\operatorname{mat}(T^is^{(0)i}))$,
--   $$
--   (x^{(0)})^Td_s + (s^{(0)})^Td_x + \tau^{(0)}d_\kappa + \kappa^{(0)}d_\tau = e^T(X^{(0)}Td_s + S^{(0)}Td_x) + \tau^{(0)}d_\kappa + \kappa^{(0)}d_\tau.
--   $$
--
--   This is the first link of the chain on p. 14 that evaluates the middle term of (26): it rewrites the linear term of the complementarity gap through the fourth line of the Newton system (22).
--
--   **Formalization Note** $e^T(X^{(0)}Td_s + S^{(0)}Td_x)$ is written block by block as $\sum_i (e^i)^T\big(\operatorname{mat}(T^ix^{(0)i})T^id_s^i + \operatorname{mat}(T^is^{(0)i})T^id_x^i\big)$. The identity holds for all vectors; it uses no hypothesis from (22).
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 14, proof of Lemma 4.1, first equality of the display after 'Moreover,'

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

namespace ConicQuadIPM.NewtonStep

open Matrix

theorem p14_first_eq
    {k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (x0 s0 dx ds : (i : Fin k) → Fin (n i) → ℝ) (τ0 κ0 dτ dκ : ℝ) :
    (∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ
      = (∑ i, ConicQuadIPM.Complementarity.e1 ⬝ᵥ (ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x0 i) *ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ ds i)
            + ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s0 i) *ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ dx i)))
        + τ0 * dκ + κ0 * dτ := by sorry

end ConicQuadIPM.NewtonStep
