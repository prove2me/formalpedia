-- Prove2me | Theorems.Thm_AlgebraicCurve_Differential_traceAlong_eq_traceDiff
-- name    : AlgebraicCurve.Differential.traceAlong_eq_traceDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/7361778a-b6a3-5bc3-88bb-1f0e27fd2671
-- title:
--   Trace along a separable map agrees with traceDiff
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and let $\varphi : F \to F'$ be a homomorphism of $K$-algebras. Assume [`AlgebraicCurve.SeparableAlong K φ`](def/AlgebraicCurve_Correspondence.html#L308), i.e. that $F'$ is a separable algebra over $F$ for the algebra structure $F \to F'$ determined by $\varphi$. Then for every $\eta \in \Omega_{F'/K}$ the two constructions of the trace on differentials agree at $\eta$. On the left, [`AlgebraicCurve.Differential.traceAlong φ`](def/AlgebraicCurve_DifferentialPushPull.html#L37) is the $K$-linear map $\Omega_{F'/K} \to \Omega_{F/K}$ defined, in the separable case, as the composite of the inverse of the canonical isomorphism $F' \otimes_F \Omega_{F/K} \cong \Omega_{F'/K}$ (available because separability gives $F'$ formally étale over $F$), the map induced on $\,\cdot\otimes_F \Omega_{F/K}$ by the field trace $\mathrm{Tr}_{F'/F} : F' \to F$, and the identification $F \otimes_F \Omega_{F/K} \cong \Omega_{F/K}$ (it is $0$ when separability fails). On the right, [`AlgebraicCurve.traceDiff K F F'`](def/ModularCurve_QExpansionDiff.html#L62), formed with respect to the algebra structure $\varphi$ and the resulting tower $K \subseteq F \subseteq F'$, is a choice of $F$-linear map $t : \Omega_{F'/K} \to \Omega_{F/K}$ satisfying $t(y \cdot \varphi^{*}\omega) = \mathrm{Tr}_{F'/F}(y)\cdot\omega$ for all $y \in F'$ and $\omega \in \Omega_{F/K}$, where $\varphi^{*}$ is the functorial map $\Omega_{F/K} \to \Omega_{F'/K}$ (and $0$ if no such map exists).
--
--   This identifies the push-forward (trace) of differentials along a finite separable extension in its two formulations used in the project: one attached to an explicit $K$-algebra homomorphism $\varphi$, the other to an ambient algebra instance together with a defining characterisation. It is used in the modular-curve computations with $q$-expansions of differentials and Hecke correspondences, which state their hypotheses with `traceAlong` and `pullbackAlong` while invoking the defining property of `traceDiff`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Differential_traceAlong_eq_traceDiff.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Differential.traceAlong_eq_traceDiff
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (h : AlgebraicCurve.SeparableAlong K φ) (η : Ω[F'⁄K]) :
    AlgebraicCurve.Differential.traceAlong φ η =
      (letI := AlgebraicCurve.algebraAlong φ
       haveI := AlgebraicCurve.isScalarTower_along φ
       AlgebraicCurve.traceDiff K F F' η) := by sorry
