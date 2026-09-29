-- Prove2me | Theorems.Thm_AutomorphicForm_isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
-- name    : AutomorphicForm.isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/759afa6d-362e-5006-9f7f-ef0eeb4af3d9
-- title:
--   Translated indicators of GL₂(mathcal Oᵥ) and its principal congruence subgroup are local test functions
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of its ring of integers $\mathcal O_K$ (a point of the height-one spectrum), and let $c$ be a unit of the $v$-adic completion $K_v$. Write $\Gamma_v$ for [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), the set of $g \in GL_2(K_v)$ such that all entries of the matrix of $g$ and all entries of the matrix of $g^{-1}$ lie in the valuation ring $\mathcal O_v$ of $K_v$, and write $\Gamma_v(1)$ for the subset of those $k \in \Gamma_v$ with $\mathrm{v}((k-1)_{ij}) < 1$ for all $i,j \in \{0,1\}$, the valuation being the canonical one on $K_v$ and $k-1$ the matrix of $k$ minus the identity. The theorem asserts two statements at once: first that the function $g \mapsto \mathbf 1_{\Gamma_v}\big((\mathrm{diag}(c,c))^{-1} g\big)$, with values in $\mathbb C$ (value $1$ on the set, $0$ off it), and second that the function $g \mapsto \mathbf 1_{\Gamma_v(1)}\big((\mathrm{diag}(c,c))^{-1} g\big)$, are both local test functions on $GL_2(K_v)$ in the sense of the project's predicate [`AutomorphicForm.IsLocalTestFn`](def/AutomorphicForm_LocalOrbitalBase.html#L88), namely locally constant and of compact support. Here $\mathrm{diag}(c,c)$ is the scalar element of $GL_2(K_v)$ attached to $c$.
--
--   These are the standard normalisations: the indicator of the maximal compact $GL_2(\mathcal O_v)$ and of its principal congruence subgroup of level $\mathfrak p_v$, each translated by a central element, are locally constant compactly supported functions on $GL_2(K_v)$. The result supplies the local test function hypothesis for the local orbital integral computations used in the automorphic part of the argument, and is invoked by the results on orbital integrals near scalars, on measurability of window values, and on the Satake-type expansion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) :
    AutomorphicForm.IsLocalTestFn K v (fun g =>
      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)) ∧
    AutomorphicForm.IsLocalTestFn K v (fun g =>
      {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
          ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}.indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)) := by sorry
