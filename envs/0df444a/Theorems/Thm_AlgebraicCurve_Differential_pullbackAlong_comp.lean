-- Prove2me | Theorems.Thm_AlgebraicCurve_Differential_pullbackAlong_comp
-- name    : AlgebraicCurve.Differential.pullbackAlong_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/775e2504-8191-5357-8e4d-8b1cc5051a02
-- title:
--   Functoriality of pull-back of Kähler differentials
-- statement:
--   Let $K$ be a field and let $F$, $F'$, $F''$ be fields equipped with $K$-algebra structures. Let $\varphi \colon F \to F'$ and $\psi \colon F' \to F''$ be homomorphisms of $K$-algebras, and let $\omega$ be an element of the module of Kähler differentials $\Omega_{F/K}$. Here, for a $K$-algebra homomorphism $\varphi \colon F \to F'$, the map [`AlgebraicCurve.Differential.pullbackAlong`](def/AlgebraicCurve_DifferentialPushPull.html#L16) $\varphi$ is the $K$-linear map $\Omega_{F/K} \to \Omega_{F'/K}$ obtained from Mathlib's `KaehlerDifferential.map` for the algebra structure on $F'$ over $F$ given by $\varphi$ (with $K \to F \to F'$ a scalar tower), restricted to scalars in $K$; on generators it sends $f\,\mathrm{d}g$ to $\varphi(f)\,\mathrm{d}\varphi(g)$. The assertion is the equality of elements of $\Omega_{F''/K}$ $$\mathrm{pullbackAlong}(\psi \circ \varphi)(\omega) = \mathrm{pullbackAlong}(\psi)\bigl(\mathrm{pullbackAlong}(\varphi)(\omega)\bigr),$$ where $\psi \circ \varphi$ denotes the composite $K$-algebra homomorphism $F \to F''$. No finiteness, separability or integrality hypothesis on $\varphi$ or $\psi$ is imposed; the statement is pointwise in $\omega$ rather than an equality of $K$-linear maps.
--
--   This is the functoriality (contravariant composition rule) for the pull-back of differentials along $K$-algebra maps of function fields, in the pointwise form used for bookkeeping when identities between differentials are transported along isomorphisms or inclusions of function fields. It is used in the treatment of modular curves, notably when comparing Kähler differentials with differentials obtained from correspondences and degeneracy maps, and in the analysis of Hecke correspondences on reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Differential_pullbackAlong_comp.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Differential.pullbackAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'') (ω : Ω[F⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (ψ.comp φ) ω =
      AlgebraicCurve.Differential.pullbackAlong ψ (AlgebraicCurve.Differential.pullbackAlong φ ω) := by sorry
