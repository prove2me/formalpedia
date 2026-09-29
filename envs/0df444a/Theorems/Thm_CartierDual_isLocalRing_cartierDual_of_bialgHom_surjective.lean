-- Prove2me | Theorems.Thm_CartierDual_isLocalRing_cartierDual_of_bialgHom_surjective
-- name    : CartierDual.isLocalRing_cartierDual_of_bialgHom_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/5ba4b868-af9a-5310-9cf6-37ddb7428e47
-- title:
--   Local Cartier dual descends to quotient Hopf algebras
-- statement:
--   Let $R$ be a commutative ring and let $H$ and $H_V$ be commutative rings carrying Hopf algebra structures over $R$ which are finite and free as $R$-modules and whose comultiplications are cocommutative, with $H_V$ nontrivial. Let $\pi : H \to H_V$ be a morphism of $R$-bialgebras (`H →ₐc[R] HV`) which is surjective as a function. Here [`CartierDual R A`](def/HopfAlgebra_CartierDual.html#L12) is by definition the $R$-linear dual `Module.Dual R A` of a commutative $R$-bialgebra $A$, equipped with the commutative ring structure dual to the coalgebra structure of $A$ (multiplication transposing the comultiplication, with the counit as unit), so that for a finite free Hopf algebra it is the coordinate algebra of the Cartier dual group scheme. The hypothesis is that the ring [`CartierDual R H`](def/HopfAlgebra_CartierDual.html#L12) is a local ring; the conclusion is that [`CartierDual R HV`](def/HopfAlgebra_CartierDual.html#L12) is a local ring as well. Note that no flatness or faithful flatness of $\pi$ beyond the stated finite freeness of the two Hopf algebras is assumed.
--
--   In the language of group schemes this says that if the Cartier dual of a finite free commutative cocommutative Hopf algebra is connected (local coordinate ring), then the same holds for the Cartier dual of any quotient Hopf algebra, i.e. for the Cartier dual of a closed subgroup scheme of the dual. It is used in the construction of the local-local models occurring in the analysis of Hecke torsion in $J_0(N)$ and in the Dieudonné-module step [`Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer`](thm.html#Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_isLocalRing_cartierDual_of_bialgHom_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CartierDual.isLocalRing_cartierDual_of_bialgHom_surjective
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    (HV : Type) [CommRing HV] [HopfAlgebra R HV] [Module.Finite R HV] [Module.Free R HV]
    [Coalgebra.IsCocomm R HV] [Nontrivial HV]
    (π : H →ₐc[R] HV) (hπ : Function.Surjective π)
    (hdual : IsLocalRing (CartierDual R H)) :
    IsLocalRing (CartierDual R HV) := by sorry
