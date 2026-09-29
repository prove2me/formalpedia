-- Prove2me | Theorems.Thm_CartierDual_algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
-- name    : CartierDual.algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b776f3a3-2e55-5059-8480-157315260e9e
-- title:
--   Cartier-dual points of a reduced p^N-killed Hopf algebra
-- statement:
--   Let $p$ be a prime and let $E$ be a commutative ring carrying the structure of a Hopf algebra over $\mathbb{Z}/p$ whose comultiplication is cocommutative and which is finite as a $\mathbb{Z}/p$-module. Let $N$ be a natural number and assume the multiplication-by-$p^N$ endomorphism of $E$, namely [`PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) E (p ^ N)`](def/PDivisibleGroup_Basic.html#L16), defined as the $p^N$-th convolution power of the identity algebra endomorphism of $E$, coincides with the composite of the counit $\varepsilon : E \to \mathbb{Z}/p$ followed by the structure map $\mathbb{Z}/p \to E$; in other words $[p^N]^{*} = \eta \circ \varepsilon$. Assume further that $E$ is reduced. Let $\kappa$ be a reduced commutative $\mathbb{Z}/p$-algebra, let $\chi$ be a $\mathbb{Z}/p$-algebra homomorphism from [`CartierDual (ZMod p) E`](def/HopfAlgebra_CartierDual.html#L12), which is by definition the $\mathbb{Z}/p$-linear dual $\mathrm{Hom}_{\mathbb{Z}/p}(E, \mathbb{Z}/p)$ with its Cartier-dual ring structure, to $\kappa$, and let $\varphi$ be an element of that Cartier dual. Then $\chi(\varphi)$ is the image under $\mathbb{Z}/p \to \kappa$ of the scalar $\varphi(1)$; that is, every $\kappa$-point of the Cartier dual of $E$ is the trivial one.
--
--   This is the statement that the Cartier dual of an étale $p$-power-torsion finite group scheme over $\mathbb{F}_p$ is infinitesimal, so that its points with values in a reduced ring are all trivial. It feeds the Cartier-dual reading of a Verschiebung identity, being cited by [`CartierDual.algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp`](thm.html#CartierDual.algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
    (p : ℕ) [Fact p.Prime]
    (E : Type) [CommRing E] [HopfAlgebra (ZMod p) E] [Coalgebra.IsCocomm (ZMod p) E] [Module.Finite (ZMod p) E]

    (N : ℕ) (hkill : PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) E (p ^ N) =
      (Algebra.ofId (ZMod p) E).comp (Bialgebra.counitAlgHom (ZMod p) E))
    (hE : IsReduced E)
    (κ : Type) [CommRing κ] [Algebra (ZMod p) κ] [IsReduced κ]
    (χ : CartierDual (ZMod p) E →ₐ[ZMod p] κ) (φ : CartierDual (ZMod p) E) :
    χ φ = algebraMap (ZMod p) κ (φ 1) := by sorry
