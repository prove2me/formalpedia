-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl
-- name    : AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/925161e6-b97d-55b4-be0d-d61aa6068e20
-- title:
--   Supportedness in U is an open condition on divisors
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes, let $r$ be a natural number and let $U$ be an open subscheme of $\mathcal{C}$. Recall that `RelEffCartierDiv.functor f r` is the presheaf on schemes sending $T$ to the set of pairs consisting of a morphism $g \colon T \to S$ together with a datum $D$ of an ideal sheaf on $\mathcal{C} \times_S T$ whose associated closed subscheme, mapped to $T$ by the second projection, is finite, flat and locally of finite presentation and has fibre rank exactly $r$ at every point of $T$, functoriality being given by pulling the ideal sheaf back along the induced morphism of products; and that `RelEffCartierDiv.supportedIn f r U` is the subfunctor cut out by the condition that the support of the ideal sheaf of $D$ be contained in the preimage of $U$ under the first projection $\mathcal{C} \times_S T \to \mathcal{C}$. The assertion is that the inclusion morphism `(RelEffCartierDiv.supportedIn f r U).ι` of this subfunctor into `RelEffCartierDiv.functor f r` has the property `IsOpenImmersion.presheaf`: it is relatively representable, and every base change of it along a morphism from a representable presheaf is (representable by) an open immersion of schemes. No hypotheses are imposed on $f$, on $r$ or on $U$.
--
--   This is the statement that, for a family of relative effective Cartier divisors of degree $r$, the locus in the base over which the divisor is supported in a given open $U \subseteq \mathcal{C}$ is open, in the functorial form needed to apply representability criteria: the inclusion of the subfunctor is relatively representable by open immersions. It is used in the construction of a universal relative effective divisor, [`AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl.lean

import Mathlib.AlgebraicGeometry.Sites.Representability
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (U : 𝒞.Opens) :
    IsOpenImmersion.presheaf (RelEffCartierDiv.supportedIn f r U).ι := by sorry
