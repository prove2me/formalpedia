-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_hasValue_norm_along_of_separableAlong
-- name    : AlgebraicCurve.Place.hasValue_norm_along_of_separableAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/bbfa079f-c777-5fcf-a9d3-af2f038e7cdc
-- title:
--   Value of a norm at a place below a separable covering
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ $K$-algebras, and assume $F'$ has principal divisors over $K$: every $g \neq 0$ in $F'$ admits a finitely supported function $D$ on places of $F'/K$ with $D(w) = \mathrm{ord}_w(g)$ for every place $w$ and with $\deg D = 0$. Let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, and regard $F'$ as an $F$-algebra through $\varphi$; assume $F'$ is a finite $F$-module and separable over $F$. Let $v$ be a place of $F/K$, i.e. a valuation subring of $F$ containing $\varphi$-compatibly the image of $K$, distinct from $F$ and a principal ideal ring. Let $g \in F'$ and let $a$ assign to each place of $F'/K$ a unit of $K$, and suppose that for every $w$ in the (finite) fibre of places of $F'/K$ restricting along $\varphi$ to $v$, the element $g$ lies in the valuation ring of $w$ and its residue is the image of $a(w)$ in the residue field of $w$. Then $\mathrm{N}_{F'/F}(g)$ lies in the valuation ring of $v$ and its residue is the image of $\prod_{w \mid v} a(w)^{e(w|v) f(w|v)} \in K$, where $e(w|v)$ is the least $n > 0$ of the form $\mathrm{ord}_w(\varphi(f))$ with $f \in F$ nonzero, and $f(w|v)$ is the degree of the residue field of $w$ over that of $v$.
--
--   This is the place-theoretic form of the classical decomposition of a field norm into local contributions, $\mathrm{ord}$- and residue-wise: constant values above multiply up with exponents $ef$, the relevant total being $[F':F]$ by the fundamental identity of ramification theory, which here is available because the covering is finite and separable. It is used in the construction of glued degree-zero divisor classes, through [`AlgebraicCurve.GluingData.isGluedPrincipal_pushforwardMap_of_separableAlong`](thm.html#AlgebraicCurve.GluingData.isGluedPrincipal_pushforwardMap_of_separableAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_hasValue_norm_along_of_separableAlong.lean

import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve in

theorem AlgebraicCurve.Place.hasValue_norm_along_of_separableAlong
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (v : Place K F) (g : F') (a : Place K F' → Kˣ)
    (ha : ∀ w ∈ Place.fiberAlong φ hφ v, w.HasValue g (a w)) :
    letI := algebraAlong φ
    v.HasValue (Algebra.norm F g)
      (∏ w ∈ Place.fiberAlong φ hφ v,
        (a w : K) ^ (w.ramificationIndexAlong φ * w.inertiaDegAlong φ hφ)) := by sorry
