-- Prove2me | Theorems.Thm_Bialgebra_snd_mul_withConv_algHom_dualNumber_eq_add
-- name    : Bialgebra.snd_mul_withConv_algHom_dualNumber_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/c7e715c3-2428-58bb-972e-6031b7c9ae73
-- title:
--   Convolution of k[ε]-points over the counit adds ε-components
-- statement:
--   Let $k$ be a commutative ring and $B$ a commutative ring carrying a $k$-bialgebra structure, with counit algebra map $\varepsilon =$ `Bialgebra.counitAlgHom k B : B →ₐ[k] k`. Let $D_1, D_2 \colon B \to k[\epsilon]$ be $k$-algebra homomorphisms into the dual numbers $k[\epsilon] =$ `DualNumber k` (the trivial square-zero extension of $k$ by $k$), and assume that each lies over the counit in the sense that the first component satisfies $\mathrm{fst}(D_1 b) = \varepsilon(b)$ and $\mathrm{fst}(D_2 b) = \varepsilon(b)$ for all $b \in B$. Fix $b \in B$. The assertion is that the second ($\epsilon$-) component of the convolution product of $D_1$ and $D_2$, formed in the multiplicative structure `WithConv` on algebra maps from a bialgebra to a commutative algebra (the product $m \circ (D_1 \otimes D_2) \circ \Delta$, transported along `WithConv.toConv` and `WithConv.ofConv`), evaluated at $b$, equals $\mathrm{snd}(D_1 b) + \mathrm{snd}(D_2 b)$. Thus writing $D_i(b) = \varepsilon(b) + \partial_i(b)\epsilon$, one has $\partial_{D_1 * D_2}(b) = \partial_1(b) + \partial_2(b)$.
--
--   This is the standard fact that the group law on the $k[\epsilon]$-points of an affine group scheme lying over the unit section induces addition on derivations, i.e. that the tangent space at the identity is a $k$-module with the group law as addition. It is used in the identification of cotangent/tangent data for a model of a modular curve, via [`ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq`](thm.html#ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_snd_mul_withConv_algHom_dualNumber_eq_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Bialgebra.snd_mul_withConv_algHom_dualNumber_eq_add
    (k : Type) [CommRing k] (B : Type) [CommRing B] [Bialgebra k B]
    (D₁ D₂ : B →ₐ[k] DualNumber k)
    (h₁ : ∀ b : B, TrivSqZeroExt.fst (D₁ b) = Bialgebra.counitAlgHom k B b)
    (h₂ : ∀ b : B, TrivSqZeroExt.fst (D₂ b) = Bialgebra.counitAlgHom k B b) (b : B) :
    TrivSqZeroExt.snd (WithConv.ofConv (WithConv.toConv D₁ * WithConv.toConv D₂) b) =
      TrivSqZeroExt.snd (D₁ b) + TrivSqZeroExt.snd (D₂ b) := by sorry
