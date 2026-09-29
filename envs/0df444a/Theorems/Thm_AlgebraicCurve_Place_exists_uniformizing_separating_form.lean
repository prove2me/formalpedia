-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_uniformizing_separating_form
-- name    : AlgebraicCurve.Place.exists_uniformizing_separating_form
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/269f3009-6baa-5d59-9466-48d8809aef14
-- title:
--   Existence of a uniformizing, separating linear form
-- statement:
--   Let $k$ and $F$ be fields with $F$ a $k$-algebra, and let $v$ be a place of $F$ over $k$, i.e. a valuation subring of $F$ containing $\operatorname{algebraMap} k F$, different from $F$ itself and a principal ideal ring; write $\operatorname{ord}_v$ for the associated order function, the negative of the logarithm of the adic valuation attached to $v$. Given $j \in F$, a natural number $n$, a family $\beta : \mathrm{Fin}\,n \to F$, a scalar $c_v \in k$ with $\operatorname{ord}_v(j - c_v) > 0$, and scalars $\beta_{v,i} \in k$ such that for each $i$ either $\beta_i = \beta_{v,i}$ in $F$ or $\operatorname{ord}_v(\beta_i - \beta_{v,i}) > 0$, assume that one of these differences is a uniformizer: either $\operatorname{ord}_v(j - c_v) = 1$ or $\operatorname{ord}_v(\beta_i - \beta_{v,i}) = 1$ for some $i$. Let further $r$ places $p_t$ of $F$ over $k$ be given together with scalars $c_t \in k$ and families $\beta_{t,\bullet} : \mathrm{Fin}\,n \to k$ such that whenever $p_t \neq v$ one has $c_t \neq c_v$ or $\beta_{t,\bullet} \neq \beta_{v,\bullet}$. Finally let $\theta : \mathrm{Fin}\,a \to k$ be injective with $n(r+1) < a$. Then there is an index $s$ such that, putting $L = j + \sum_{i} \theta_s^{\,i+1}\beta_i$ and $L(v) = c_v + \sum_i \theta_s^{\,i+1}\beta_{v,i}$, one has $\operatorname{ord}_v(L - L(v)) = 1$, and for every $t$ with $p_t \neq v$ the scalar $c_t + \sum_i \theta_s^{\,i+1}\beta_{t,i}$ differs from $L(v)$.
--
--   This is the elementary general-position step in the theory of algebraic function fields: among the linear combinations $j + \sum_i \theta^{i+1}\beta_i$ with $\theta$ ranging over sufficiently many distinct scalars, one may be chosen whose difference from its value at $v$ is a uniformizer at $v$ and whose prescribed values at the finitely many auxiliary places all differ from its value at $v$. It is used in the proof of [`AlgebraicCurve.Divisor.exists_symmValue_rows_kernel_iff`](thm.html#AlgebraicCurve.Divisor.exists_symmValue_rows_kernel_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_uniformizing_separating_form.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_uniformizing_separating_form
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (v : Place k F) {j : F} {n : ℕ} (β : Fin n → F)
    (cv : k) (hcv : 0 < v.ord (j - algebraMap k F cv))
    (βv : Fin n → k)
    (hβv : ∀ i, β i = algebraMap k F (βv i) ∨ 0 < v.ord (β i - algebraMap k F (βv i)))
    (hU1 : v.ord (j - algebraMap k F cv) = 1 ∨ ∃ i, v.ord (β i - algebraMap k F (βv i)) = 1)
    {r : ℕ} (pt : Fin r → Place k F) (cpt : Fin r → k) (βpt : Fin r → Fin n → k)
    (hS1 : ∀ t, pt t ≠ v → cpt t ≠ cv ∨ βpt t ≠ βv)
    {a : ℕ} (θ : Fin a → k) (hθ : Function.Injective θ) (ha : n * (r + 1) < a) :
    ∃ s : Fin a,
      v.ord ((j + ∑ i : Fin n, algebraMap k F (θ s ^ (i.val + 1)) * β i)
          - algebraMap k F (cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i)) = 1 ∧
      ∀ t, pt t ≠ v →
        cpt t + ∑ i : Fin n, θ s ^ (i.val + 1) * βpt t i
          ≠ cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i := by sorry
