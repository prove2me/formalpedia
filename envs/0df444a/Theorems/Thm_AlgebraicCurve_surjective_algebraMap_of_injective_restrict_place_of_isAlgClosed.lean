-- Prove2me | Theorems.Thm_AlgebraicCurve_surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
-- name    : AlgebraicCurve.surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/564f46fe-b012-576e-81a9-7dca532f6ba0
-- title:
--   Injectivity on places forces a trivial finite extension
-- statement:
--   Let $K$, $F$, $F'$ be fields with $K$-algebra structures on $F$ and $F'$ and an $F$-algebra structure on $F'$ compatible with them (a scalar tower $K \subseteq F \subseteq F'$). Assume $K$ is algebraically closed of characteristic zero, that $F'$ is finite-dimensional as an $F$-module, and that each of $F$ and $F'$ is essentially of finite type over $K$ and satisfies `IsCurveOver K ·`, i.e.: every nonzero element $f$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$; for every place $v$ the residue field of its valuation subring is a finite $K$-module; and the module of Kähler differentials over $K$ is free of rank $1$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from all of $F$, and a principal ideal ring; the restriction along $F \to F'$ of a place $w$ of $F'$ is the valuation subring $w^{-1}$-pullback, namely the preimage (comap) of the valuation subring of $w$ under $\operatorname{algebraMap} F F'$. The hypothesis is that the restriction map $w \mapsto w|_F$ from places of $F'$ over $K$ to places of $F$ over $K$ is injective. The conclusion is that $\operatorname{algebraMap} F F' : F \to F'$ is surjective, i.e. $F' = F$.
--
--   This is the classical statement that a finite extension of one-variable function fields over an algebraically closed field of characteristic zero in which every place of the base has exactly one extension must be trivial: over an algebraically closed constant field all inertia degrees are $1$, so the unique place above $v$ is totally ramified of degree $[F':F]$, while in characteristic zero ramification occurs at only finitely many places. It serves as the degree-one criterion used in the Čerednik–Drinfeld part of the development, where it yields the surjectivity of a ring homomorphism between function fields of quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
    (K F F' : Type) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    [Module.Finite F F']
    (hinj : Function.Injective (fun w : Place K F' => w.restrict F)) :
    Function.Surjective (algebraMap F F') := by sorry
