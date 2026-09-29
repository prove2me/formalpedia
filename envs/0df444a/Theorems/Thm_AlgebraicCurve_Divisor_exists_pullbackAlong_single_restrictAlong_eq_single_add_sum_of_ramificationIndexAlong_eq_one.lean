-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
-- name    : AlgebraicCurve.Divisor.exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/04bf156c-0591-51db-849e-2d74bf057f05
-- title:
--   Pull-back of an unramified place: φ^*[w₀]=[W₀]+sumⱼ eⱼ[Wⱼ]
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and assume $F'$ has principal divisors over $K$, i.e. every nonzero $f \in F'$ is the divisor-data of some finitely supported function on places of $F'$ agreeing with $v \mapsto v.\mathrm{ord}\,f$ and of degree $0$. Let $\varphi : F \to F'$ be a $K$-algebra map whose underlying ring homomorphism is integral; via $\varphi$ regard $F'$ as an $F$-algebra and assume it is a finite and separable $F$-algebra, with $\dim_F F' = n+1$ for some natural number $n$. Assume every place $W$ of $F'$ over $K$ has inertia degree $1$ along $\varphi$, that is, the residue field of $W$ has $F$-rank $1$ over the residue field of the place of $F$ obtained by pulling back the valuation subring along $\varphi$. Let $W_0$ be a place of $F'$ whose ramification index along $\varphi$ (the least $m>0$ such that $W_0.\mathrm{ord}(\varphi f) = m$ for some $f \neq 0$ in $F$) equals $1$. Then there exist $k \in \mathbb{N}$, an injective family $W : \mathrm{Fin}\,k \to$ places of $F'$ and positive integers $e_j$ with $\sum_j e_j = n$, such that each $W_j \neq W_0$, each $W_j$ restricts along $\varphi$ to $w_0 := W_0$ restricted along $\varphi$, every place of $F'$ restricting to $w_0$ is $W_0$ or some $W_j$, the ramification index of $W_j$ along $\varphi$ is $e_j$, and the pull-back of the divisor $1 \cdot [w_0]$ along $\varphi$ equals $[W_0] + \sum_j e_j [W_j]$.
--
--   This is the standard computation of the conorm (divisor pull-back) of a prime divisor in a finite separable extension of function fields, specialised to the case of trivial residue extensions and a place $W_0$ unramified over $w_0$: the fibre over $w_0$ consists of $W_0$ together with finitely many further places whose ramification indices sum to $\deg\varphi - 1$. It is used in the analysis of the generic fibre of a degeneracy map of modular curves, in [`ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow`](thm.html#ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (n : ℕ) (hn : finrankAlong K φ = n + 1)
    (hinert : ∀ W : Place K F', W.inertiaDegAlong φ hφ = 1)
    (W₀ : Place K F') (he : W₀.ramificationIndexAlong φ = 1) :
    ∃ (k : ℕ) (W : Fin k → Place K F') (e : Fin k → ℕ),
      (∀ j, 0 < e j) ∧ ∑ j, e j = n ∧ Function.Injective W ∧
      (∀ j, W j ≠ W₀) ∧ (∀ j, (W j).restrictAlong φ hφ = W₀.restrictAlong φ hφ) ∧
      (∀ W' : Place K F', W'.restrictAlong φ hφ = W₀.restrictAlong φ hφ → W' = W₀ ∨ ∃ j, W' = W j) ∧
      (∀ j, (W j).ramificationIndexAlong φ = e j) ∧
      Divisor.pullbackAlong φ hφ (Finsupp.single (W₀.restrictAlong φ hφ) 1) =
        Finsupp.single W₀ 1 + ∑ j, (e j : ℤ) • Finsupp.single (W j) 1 := by sorry
