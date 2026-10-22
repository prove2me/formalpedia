-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
-- name    : BirkhoffGlobalSection.TangentialHessian.leviCivita_explicit_derivatives
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:40:24.061981+00:00
-- url     : https://prove2.me/theorems/87df482a-9a8b-470a-94d9-defec66f8def
-- title:
--   Explicit first and second derivatives of the Levi-Civita Hamiltonian $K_{\mu,c}$
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   Let $\nabla K$ and $\nabla^2K$ denote the explicit gradient and Hessian formulas `kGrad`, `kHess` of the module `Def_BirkhoffGlobalSection_TangentialHessian`. For all real $\mu,c$ the following hold.
--
--   1. For every $s\in U$ and every coordinate $i$, the partial derivative of the Levi-Civita Hamiltonian is
--   $$
--   \partial_i K_{\mu,c}(s)=\nabla K_{\mu,c}(s)_i .
--   $$
--   2. For every $s\in U$ and all $u,v\in\mathbb R^4$, the iterated directional derivative is
--   $$
--   D\big(x\mapsto DK_{\mu,c}(x)[u]\big)(s)[v]=\sum_{k,l}u_k\,v_l\,\nabla^2K_{\mu,c}(s)_{kl}.
--   $$
--   3. The maps $s\mapsto\nabla K_{\mu,c}(s)$ and $s\mapsto\nabla^2K_{\mu,c}(s)$ are continuous on $U$.
--
--   These identities turn the tangential-Hessian condition of Proposition 4.4, which is stated with Fréchet derivatives, into explicit algebraic expressions.
--
--   **Formalization Note.** Derivatives are Mathlib `fderiv`s on $\mathrm{Phase}=\mathrm{Fin}\,4\to\mathbb R$, and `partialDerivative` is the platform's `fderiv` along a coordinate vector.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, eq. (2.2); explicit derivatives used for the tangential Hessian of Section 2.3 and Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.Topology.Instances.Matrix

namespace BirkhoffGlobalSection.TangentialHessian

/-- Explicit first and second derivatives of the Levi-Civita Hamiltonian away from the
second collision, and continuity of the explicit formulas there. -/
theorem leviCivita_explicit_derivatives (μ c : ℝ) :
    (∀ s ∈ U, ∀ i : Fin 4,
      partialDerivative (leviCivitaHamiltonian μ c) s i = kGrad μ c s i) ∧
    (∀ s ∈ U, ∀ u v : Phase,
      fderiv ℝ (fun x => fderiv ℝ (leviCivitaHamiltonian μ c) x u) s v =
        ∑ k, ∑ l, u k * v l * kHess μ c s k l) ∧
    ContinuousOn (kGrad μ c) U ∧ ContinuousOn (kHess μ c) U := by sorry

end BirkhoffGlobalSection.TangentialHessian
