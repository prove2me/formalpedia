-- Prove2me | Theorems.Thm_AsymptoticOperator_graphSet_add_mem
-- name    : AsymptoticOperator.graphSet_add_mem
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T11:32:45.902294+00:00
-- url     : https://prove2.me/theorems/e12d6a19-b6bd-42d9-b53c-94314a264025
-- title:
--   The graph of $-J_0\partial_t - S$ on $L^2(S^1,\mathbb{R}^{2n})$ is closed under addition
-- statement:
--   Let $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure and let $L^2_n=L^2(S^1,\mathbb R^{2n})$. For $f\in L^2_n$ and $k\in\mathbb Z$ let $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb C^{2n}$ be its $k$-th Fourier coefficient, computed componentwise after viewing the real entries of $f$ as complex numbers.
--
--   Let $J_0=\begin{pmatrix}0&-I_n\\ I_n&0\end{pmatrix}$ and let $S:S^1\to\mathbb R^{2n\times2n}$ be continuous (no symmetry is assumed). Say $f\in W^{1,2}$ if $\sum_{k\in\mathbb Z}(1+k^2)|\hat f_k|^2<\infty$, and let $\Gamma_S\subseteq L^2_n\times L^2_n$ be the set of pairs $(f,g)$ with $f\in W^{1,2}$ and
--   $$\hat g_k=-2\pi ik\,J_0\hat f_k-(Sf)^\wedge_k\qquad\text{for all }k\in\mathbb Z,$$
--   i.e. the pairs with $g=-J_0\partial_tf-Sf$ (Wendl (3.4)).
--
--   If $(f_1,g_1)\in\Gamma_S$ and $(f_2,g_2)\in\Gamma_S$, then $(f_1+f_2,\,g_1+g_2)\in\Gamma_S$.
--
--   This is the additivity half of the statement that $\Gamma_S$ is a linear subspace of $L^2_n\times L^2_n$, so that $A_S=-J_0\partial_t-S$ is a linear operator.
--
--   Formalization note: `L2 n`, `coeff`, `coeffMul`, `InW12` and `graphSet` come from the definition module `AsymptoticOperator_Setting`; `L2 n` is `Lp (EuclideanSpace ℝ (Fin n ⊕ Fin n)) 2` over `UnitAddCircle` with `AddCircle.haarAddCircle`, `coeff f k` is the vector $\hat f_k$, and `graphSet S` is the set of pairs $(f,g)$ described above.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- The relation `A_S f = g` of Wendl (3.4) is additive: the set `graphSet S` of pairs
`(f, g)` with `f ∈ W^{1,2}` and `ĝₖ = -2πik J₀ f̂ₖ - (S f)^ₖ` is closed under addition. -/
theorem graphSet_add_mem {n : ℕ} (S : C(UnitAddCircle, Mat n)) {p q : L2 n × L2 n}
    (hp : p ∈ graphSet S) (hq : q ∈ graphSet S) : p + q ∈ graphSet S := by sorry

end AsymptoticOperator
