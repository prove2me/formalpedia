-- Prove2me | Theorems.Thm_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add
-- name    : EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/37be3f3a-8caf-5da4-8af8-f54d5fd49f35
-- title:
--   Weight-one Eisenstein functions: SL₂(ℤ)-covariance and N-periodicity
-- statement:
--   Fix a positive integer $N$ and a point $\tau$ of the upper half-plane. For $v\in\mathbb Z^2$ put $$g_1^{v}(\tau)=\frac1N\Bigl(Z\bigl(\tau,\tfrac{v_0\tau+v_1}{N}\bigr)-\frac{v_0(\tau G_2(\tau)-2\pi i)+v_1G_2(\tau)}{N}\Bigr),$$ where $Z(\tau,z)=1/z+\sum_{v\neq 0}\bigl(1/(z-(v_0\tau+v_1))+1/(v_0\tau+v_1)+z/(v_0\tau+v_1)^2\bigr)$ is the Weierstrass zeta function of the lattice $\mathbb Z\tau+\mathbb Z$ (the sum being over $v\in\mathbb Z^2$, the term at $v=0$ being replaced by $0$) and $G_2$ is the weight-two Eisenstein series, these being [`EisensteinSeries.weierstrassZeta`](def/EisensteinSeries_WeierstrassZeta.html#L5) and [`EisensteinSeries.eisensteinG1`](def/EisensteinSeries_WeierstrassZeta.html#L9). The theorem asserts the conjunction of two statements. First, for every $\gamma\in SL_2(\mathbb Z)$ and every $v\in\mathbb Z^2$, $$g_1^{v}(\gamma\tau)=\mathrm{denom}(\gamma,\tau)\,g_1^{v\gamma}(\tau),$$ where $\mathrm{denom}(\gamma,\tau)=c\tau+d$ for $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ and $v\gamma$ is the vector–matrix product of the row vector $v$ with $\gamma$. Second, for all $v,w\in\mathbb Z^2$ such that it is not the case that $N$ divides every coordinate of $v$, $$g_1^{v+Nw}(\tau)=g_1^{v}(\tau).$$
--
--   These are the two defining properties of the weight-one Eisenstein functions $g_1^{v}$ of level $N$ attached to vectors $v\in\mathbb Z^2$: together they show that $v\mapsto g_1^{v}$ descends to a family indexed by the non-zero classes $v\in(\mathbb Z/N)^2$, weakly modular of weight one for $\Gamma(N)$ and permuted by the right action of $SL_2(\mathbb Z)$. They are used in establishing boundedness at $i\infty$ and the $q$-expansion of $g_1^{v}$, and ultimately in the construction of a weight-one Eisenstein series with prescribed $q$-coefficients attached to an odd primitive character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean

import Mathlib
import Definitions.Def_EisensteinSeries_WeierstrassZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real MatrixGroups Matrix

theorem EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) :
    (∀ (γ : SL(2, ℤ)) (v : Fin 2 → ℤ),
        EisensteinSeries.eisensteinG1 N v (γ • τ) =
          UpperHalfPlane.denom γ τ *
            EisensteinSeries.eisensteinG1 N (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ) ∧
    (∀ v w : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        EisensteinSeries.eisensteinG1 N (v + (N : ℤ) • w) τ =
          EisensteinSeries.eisensteinG1 N v τ) := by sorry
