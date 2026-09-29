-- Prove2me | Theorems.Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
-- name    : AlgebraicCurve.Differential.pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/bc3855d1-3f14-5846-96bc-7178b4acf0c9
-- title:
--   Swapping automorphism conjugates tr_αβ^* into tr_βα^*
-- statement:
--   Let $K$ be a field and let $F$, $F'$ be field extensions of $K$, and let $\alpha,\beta\colon F\to F'$ be $K$-algebra homomorphisms. Assume `SeparableAlong K α` and `SeparableAlong K β`, that is: when $F'$ is regarded as an $F$-algebra via $\alpha$ (respectively via $\beta$) it is a separable $F$-algebra; this is exactly the condition under which `Differential.traceAlong` is given by the composite of the inverse of the base-change isomorphism $F'\otimes_F\Omega_{F/K}\cong\Omega_{F'/K}$ (available since a separable algebra is formally étale), the algebra trace of $F'$ over $F$ applied to the left tensor factor, and the identification $F\otimes_F\Omega_{F/K}\cong\Omega_{F/K}$, rather than by $0$. Let $w$ be a $K$-algebra automorphism of $F$ and $w'$ one of $F'$, and assume the swapping relations $w'(\alpha x)=\beta(w x)$ and $w'(\beta x)=\alpha(w x)$ for all $x\in F$. Here `Differential.pullbackAlong φ` denotes the $K$-linear map $\Omega_{F/K}\to\Omega_{F'/K}$ induced on Kähler differentials by the $F$-algebra structure $\varphi$. Then for every $\omega\in\Omega_{F/K}$,
--   $$w^*\bigl(\operatorname{tr}_\alpha(\beta^*\omega)\bigr)=\operatorname{tr}_\beta\bigl(\alpha^*(w^*\omega)\bigr).$$
--
--   In the geometric picture, $\alpha$ and $\beta$ are the two projections of a correspondence between curves with function fields $F\subseteq F'$, the operators $\operatorname{tr}_\alpha\circ\beta^*$ and $\operatorname{tr}_\beta\circ\alpha^*$ are the actions on differentials of the correspondence and of its transpose, and the statement says that an automorphism of the covering field exchanging the two projections (compatibly with $w$ downstairs) conjugates one action into the other. It is used in the modular-curve part of the development, in the analysis of the action of Hecke correspondences on torsion of differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve in

theorem AlgebraicCurve.Differential.pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (α β : F →ₐ[K] F') (hα : SeparableAlong K α) (hβ : SeparableAlong K β)
    (w : F ≃ₐ[K] F) (w' : F' ≃ₐ[K] F')
    (hswapα : ∀ x : F, w' (α x) = β (w x)) (hswapβ : ∀ x : F, w' (β x) = α (w x))
    (ω : Ω[F⁄K]) :
    Differential.pullbackAlong w.toAlgHom (Differential.traceAlong α (Differential.pullbackAlong β ω)) =
      Differential.traceAlong β (Differential.pullbackAlong α (Differential.pullbackAlong w.toAlgHom ω)) := by sorry
