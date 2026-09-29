-- Prove2me | Theorems.Thm_AlgebraicCurve_pullbackDiff_smul
-- name    : AlgebraicCurve.pullbackDiff_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/786d607b-888b-5b78-a509-18f0dd290404
-- title:
--   Semilinearity of the pullback on Kähler differentials
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ both $K$-algebras, let $\varphi \colon F \to F'$ be a homomorphism of $K$-algebras, let $g \in F$ and let $\omega \in \Omega_{F/K}$ be a Kähler differential. Here `pullbackDiff φ` denotes the $K$-linear map $\Omega_{F/K} \to \Omega_{F'/K}$ obtained as follows: $\varphi$ is used to equip $F'$ with the structure of an $F$-algebra, which together with $\varphi$'s compatibility with the structure maps from $K$ makes $K \to F \to F'$ a tower; the functoriality map `KaehlerDifferential.map` for this tower, a priori $F$-linear, is then restricted to scalars in $K$. The assertion is that $\varphi$-pullback is semilinear over $\varphi$: the pullback of $g \cdot \omega$, where $g$ acts on $\Omega_{F/K}$ through its $F$-module structure, equals $\varphi(g)$ acting on the pullback of $\omega$ through the $F'$-module structure of $\Omega_{F'/K}$.
--
--   This records the $\varphi$-semilinearity of the functoriality map on modules of Kähler differentials, which is what makes arguments by induction over $F$-spans of the elements $D x$ possible, given that `pullbackDiff` carries only $K$-linearity in its type. It is used in the comparison of $q$-expansions of differentials on modular curves under trace and pullback maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_pullbackDiff_smul.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.pullbackDiff_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (g : F) (ω : Ω[F⁄K]) :
    pullbackDiff φ (g • ω) = φ g • pullbackDiff φ ω := by sorry
