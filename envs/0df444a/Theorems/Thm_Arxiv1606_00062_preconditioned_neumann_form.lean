-- Prove2me | Theorems.Thm_Arxiv1606_00062_preconditioned_neumann_form
-- name    : Arxiv1606_00062.preconditioned_neumann_form
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T22:37:11.71114+00:00
-- url     : https://prove2.me/theorems/d4ec43b9-c139-4e14-b314-bfdfa5adbdb7
-- title:
--   Theorem 8: the preconditioned equation in Neumann-series form
-- statement:
--   Let $E$ be a complex Banach space, $\mathcal T,\mathcal K:E\to E$ bounded linear operators and $g\in E$. Suppose the spectral radius of $\mathcal K$ satisfies $r(\mathcal K)<1$. Then $\mathcal I-\mathcal K$ is invertible, the Neumann series converges in operator norm with
--
--   $$(\mathcal I-\mathcal K)^{-1}=\sum_{\ell=0}^{\infty}\mathcal K^\ell,$$
--
--   the series $\sum_\ell\mathcal K^\ell(\mathcal T-\mathcal K)$ and $\sum_\ell\mathcal K^\ell g$ converge, and for every $\eta\in E$ the preconditioned equation
--
--   $$(\mathcal I-\mathcal K)^{-1}(\mathcal I-\mathcal T)\eta=(\mathcal I-\mathcal K)^{-1}g$$
--
--   holds if and only if
--
--   $$\Big(\mathcal I-\sum_{\ell=0}^{\infty}\mathcal K^\ell(\mathcal T-\mathcal K)\Big)\eta=\sum_{\ell=0}^{\infty}\mathcal K^\ell g.$$
--
--   **Formalization Note** The paper does not name the space on which $\mathcal K$ acts; Remark 12 indicates $C(\partial\Omega)$ with the supremum norm, a complex Banach space. The statement is for every complex Banach space and every bounded $\mathcal T$, $\mathcal K$. "Can be written alternatively as" is formalized as the equivalence of the two equations for every $\eta$, together with the convergence of the series and the invertibility that make both sides meaningful.
-- source:
--   Boubendir, Ecevit and Reitich, Acceleration of an iterative method for the evaluation of high-frequency multiple scattering effects, arXiv:1606.00062v1 (2016), claim c010; Section 6, Theorem 8, eqs. (36)-(38), PDF p. 13

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open Filter Topology

namespace Arxiv1606_00062

theorem preconditioned_neumann_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (T K : E →L[ℂ] E) (g : E) (hK : spectralRadius ℂ K < 1) :
    IsUnit (1 - K) ∧
    Summable (fun l : ℕ => K ^ l) ∧
    Ring.inverse (1 - K) = ∑' l : ℕ, K ^ l ∧
    Summable (fun l : ℕ => K ^ l * (T - K)) ∧
    Summable (fun l : ℕ => (K ^ l) g) ∧
    ∀ η : E, (Ring.inverse (1 - K) * (1 - T)) η = Ring.inverse (1 - K) g ↔
      (1 - ∑' l : ℕ, K ^ l * (T - K)) η = ∑' l : ℕ, (K ^ l) g := by sorry

end Arxiv1606_00062
