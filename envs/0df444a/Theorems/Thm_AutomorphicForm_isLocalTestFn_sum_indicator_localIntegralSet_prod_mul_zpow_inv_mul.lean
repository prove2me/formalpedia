-- Prove2me | Theorems.Thm_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
-- name    : AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/b0665a02-7c29-5ea6-a710-739e3c251a94
-- title:
--   Hecke-word indicator sums are local test functions
-- statement:
--   Let $K$ be a number field, let $v$ be a height-one prime of its ring of integers $\mathcal{O}_K$, and write $K_v$ for the $v$-adic completion. Fix $n \in \mathbb{N}$, a family $rT : \mathrm{Fin}\,n \to \mathrm{GL}_2(K_v)$, an element $z \in \mathrm{GL}_2(K_v)$, and $k, j \in \mathbb{N}$. Consider the complex-valued function on $\mathrm{GL}_2(K_v)$ given by $$x \mapsto \sum_{\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,n} \mathbf{1}_{S}\bigl((rT(\iota(0))\cdots rT(\iota(k-1))\, z^{j})^{-1} x\bigr),$$ where the sum runs over all $n^{k}$ functions $\iota$, the inner product is the ordered product of the listed elements $rT(\iota(i))$, and $\mathbf{1}_S$ is the indicator function taking the value $1 \in \mathbb{C}$ on $S =$ [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) and $0$ elsewhere; by definition $S$ consists of those $g \in \mathrm{GL}_2(K_v)$ for which the matrix of $g$ and the matrix of $g^{-1}$ both lie in `integralMatrixSet` over the ring of $v$-adic integers $\mathcal{O}_v \subseteq K_v$. The assertion is that this function satisfies [`AutomorphicForm.IsLocalTestFn K v`](def/AutomorphicForm_LocalOrbitalBase.html#L88), that is, it is locally constant and has compact support.
--
--   This is the statement that the function attached to a Hecke word at the finite place $v$ — a finite sum of indicators of left translates of the integral subgroup, as arises from the $k$-fold Hecke operator composed with the $j$-th power of a central or diagonal element — is a local test function on $\mathrm{GL}_2(K_v)$. It serves as an admissibility check for the local components of test functions in the local-orbital and Satake packaging, and is used in the results on orbital integrals and on Satake–Laurent expansions of Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K)) (z : GL (Fin 2) (v.adicCompletion K)) (k j : ℕ) :
    AutomorphicForm.IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
      ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x)) := by sorry
