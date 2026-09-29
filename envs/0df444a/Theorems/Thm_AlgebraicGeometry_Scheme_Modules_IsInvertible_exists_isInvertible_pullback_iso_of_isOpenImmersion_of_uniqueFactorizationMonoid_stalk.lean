-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/96cc58f8-07cd-5ce4-b0c2-b388d32c71e5
-- title:
--   Surjectivity of Pic(X)toPic(U) for locally factorial X
-- statement:
--   Let $X$ and $U$ be schemes (in the bottom universe) with $X$ integral and noetherian, and suppose that for every point $x$ of $X$ the stalk $\mathcal O_{X,x}$ of the structure presheaf is a unique factorisation monoid. Let $j : U \to X$ be an open immersion, and let $\mathcal L_U$ be an object of $U.\mathrm{Modules}$, i.e. a sheaf of modules over the sheaf of rings of $U$, which satisfies the predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $U$ there is an open subscheme $V \subseteq U$ with $x \in V$ such that the pullback of $\mathcal L_U$ along the inclusion $V \hookrightarrow U$ is isomorphic to the unit sheaf of modules of $V$ (the structure sheaf viewed as a module over itself). The conclusion asserts the existence of a sheaf of modules $\mathcal L$ on $X$ which is invertible in the same local sense — each point of $X$ has an open neighbourhood on which the restriction of $\mathcal L$ is isomorphic to the unit sheaf — together with an isomorphism (given as the nonemptiness of the type of isomorphisms) between the pullback of $\mathcal L$ along $j$ and $\mathcal L_U$.
--
--   This is the surjectivity of the restriction map $\operatorname{Pic}(X) \to \operatorname{Pic}(U)$ on an integral noetherian scheme all of whose local rings are factorial: every line bundle on an open subscheme extends to the whole scheme. It is used in the theory of good reduction of Jacobians, namely in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_pullback_iso_of_isDiscreteValuationRing`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_pullback_iso_of_isDiscreteValuationRing), where a line bundle on the generic fibre of a smooth scheme over a discrete valuation ring has to be extended over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk
    {X U : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (hfact : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (j : U ⟶ X) [IsOpenImmersion j]
    (𝓛U : U.Modules) (h𝓛U : Scheme.Modules.IsInvertible 𝓛U) :
    ∃ 𝓛 : X.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ Nonempty ((Scheme.Modules.pullback j).obj 𝓛 ≅ 𝓛U) := by sorry
