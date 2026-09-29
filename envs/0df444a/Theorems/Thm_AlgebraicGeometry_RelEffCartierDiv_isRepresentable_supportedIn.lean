-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isRepresentable_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.isRepresentable_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/ff59e1b5-2dfc-5174-beed-7e1c7c5927cf
-- title:
--   Representability of the chart of divisors supported in an affine open
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes which is separated and smooth of relative dimension $1$, let $r$ be a natural number, let $V$ be an affine open of $S$ and $U$ an affine open of $\mathcal{C}$ with $U \le f^{-1}(V)$ as opens of $\mathcal{C}$. Consider the functor $(\mathrm{Sch})^{\mathrm{op}} \to \mathrm{Type}$ sending $T$ to the set of pairs consisting of a morphism $g \colon T \to S$ together with a relative effective Cartier divisor of degree $r$ for $f$ over $g$, that is, an ideal sheaf datum $I$ on $\mathcal{C} \times_S T$ such that the closed immersion of the associated closed subscheme followed by $\mathrm{pr}_2 \colon \mathcal{C} \times_S T \to T$ is finite, flat and locally of finite presentation, with fibre rank equal to $r$ at every point of $T$; the functoriality is by pullback of the ideal sheaf datum along the induced map of products. The assertion is that its subfunctor of those pairs $(g, D)$ whose support, as a subset of $\mathcal{C} \times_S T$, is contained in the preimage of $U$ under $\mathrm{pr}_1$, is representable: there is a scheme $X$, affine whenever $r > 0$, together with an isomorphism of this subfunctor with $\mathrm{Hom}(-, X)$, natural in $T$.
--
--   This is the local representability statement for the functor of relative effective Cartier divisors of degree $r$ on a smooth separated relative curve, giving the affine charts indexed by affine opens $U \subseteq f^{-1}(V)$ out of which the divisor scheme $\mathrm{Div}^r_{\mathcal{C}/S}$ is glued. It is used in the construction of a universal relative effective Cartier divisor, and in the statement producing affine opens of the representing scheme attached to finite sets of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isRepresentable_supportedIn.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isRepresentable_supportedIn
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ)
    (V : S.affineOpens) (U : 𝒞.affineOpens) (hUV : (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)) :
    ∃ X : Scheme.{u}, (0 < r → IsAffine X) ∧
      Nonempty ((RelEffCartierDiv.supportedIn f r U).toFunctor.RepresentableBy X) := by sorry
