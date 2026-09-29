-- Prove2me | Theorems.Thm_Bialgebra_fst_mul_withConv_algHom_dualNumber_eq_counit
-- name    : Bialgebra.fst_mul_withConv_algHom_dualNumber_eq_counit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/06ff22f6-1065-59d7-903f-f036fa877d4d
-- title:
--   Convolution of two dual-number points over the counit lies over the counit
-- statement:
--   Let $k$ be a commutative ring and $B$ a commutative ring carrying a $k$-bialgebra structure, with counit the $k$-algebra map $\varepsilon =$ `Bialgebra.counitAlgHom k B` $\colon B \to k$, and let $k[\epsilon] =$ `DualNumber k` be the dual numbers over $k$, i.e. the trivial square-zero extension of $k$ by $k$, whose first-component projection is `TrivSqZeroExt.fst`. Let $D_1, D_2 \colon B \to k[\epsilon]$ be $k$-algebra homomorphisms, and assume that each lies over the counit in the sense that for every $b \in B$ one has $\mathrm{fst}(D_1 b) = \varepsilon(b)$ and $\mathrm{fst}(D_2 b) = \varepsilon(b)$. Let $b \in B$. The conclusion is that the product of $D_1$ and $D_2$ formed in the convolution monoid structure on the algebra maps $B \to k[\epsilon]$ (the type synonym `WithConv`, whose multiplication is $D_1 * D_2 = m \circ (D_1 \otimes D_2) \circ \Delta$, transported back along `WithConv.ofConv`) again lies over the counit at $b$: the first component of $(D_1 * D_2)(b)$ equals $\varepsilon(b)$. The assertion is pointwise in the given $b$, not stated as an equality of algebra maps.
--
--   This is one half of the standard dictionary identifying the $k[\epsilon]$-points of an affine group scheme lying over the unit section with the Lie algebra, the group law on such points being convolution: it records that the convolution product of two such points again lies over the unit. It is used in the computation of the cotangent space of a model of a modular curve, via [`ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq`](thm.html#ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_fst_mul_withConv_algHom_dualNumber_eq_counit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Bialgebra.fst_mul_withConv_algHom_dualNumber_eq_counit
    (k : Type) [CommRing k] (B : Type) [CommRing B] [Bialgebra k B]
    (D₁ D₂ : B →ₐ[k] DualNumber k)
    (h₁ : ∀ b : B, TrivSqZeroExt.fst (D₁ b) = Bialgebra.counitAlgHom k B b)
    (h₂ : ∀ b : B, TrivSqZeroExt.fst (D₂ b) = Bialgebra.counitAlgHom k B b) (b : B) :
    TrivSqZeroExt.fst (WithConv.ofConv (WithConv.toConv D₁ * WithConv.toConv D₂) b) =
      Bialgebra.counitAlgHom k B b := by sorry
