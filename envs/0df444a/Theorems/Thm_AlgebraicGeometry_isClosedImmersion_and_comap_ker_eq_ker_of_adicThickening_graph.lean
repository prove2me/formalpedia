-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph
-- name    : AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/cfabcdc1-55c3-52f0-9336-1f7ba8de6583
-- title:
--   Graphs of compatible morphisms of adic thickenings are closed immersions
-- statement:
--   Let $R$ be a commutative ring, $I \subseteq R$ an ideal, and let $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$ be morphisms of schemes with $g$ separated. For a morphism $h$ to $\operatorname{Spec} R$ write $h_n$ for `adicThickening h I n`, the pullback of $h$ along $\operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$, with `adicThickeningToBase h I n` its projection to $\operatorname{Spec}(R/I^{n+1})$, `adicThickeningι h I n` its projection to the source of $h$, and `adicThickeningTransition h I n` the morphism from the $n$-th to the $(n+1)$-st thickening induced by $R/I^{n+2} \to R/I^{n+1}$. Assume given morphisms $\varphi_n : X_n \to Y_n$ commuting with the projections to $\operatorname{Spec}(R/I^{n+1})$ and with the transition morphisms, i.e. $\mathrm{transition}_n \,;\, \varphi_{n+1} = \varphi_n \,;\, \mathrm{transition}_n$; write $p = \mathrm{pr}_X \,;\, f$ for the structure morphism of $X \times_{\operatorname{Spec} R} Y$ obtained from `pullback.fst f g` followed by $f$, and assume given morphisms $\gamma_n : X_n \to (X\times_R Y)_n$ such that $\gamma_n$ followed by the projection of $(X\times_R Y)_n$ to $X \times_R Y$ and then $\mathrm{pr}_X$ equals `adicThickeningι f I n`, and the same composite with $\mathrm{pr}_Y$ equals $\varphi_n$ followed by `adicThickeningι g I n`. Then for every $n$: $\gamma_n$ is a closed immersion, and the ideal sheaf data $\ker \gamma_{n+1}$ pulled back (`comap`) along `adicThickeningTransition p I n` equals $\ker \gamma_n$.
--
--   This is the standard fact that the graph of a morphism into a separated scheme is a closed immersion, in the relative form needed for adic thickenings, together with the compatibility of the resulting closed subscheme structures as the level $n$ varies. It feeds the construction of a morphism out of an $I$-adically complete base from a compatible system of morphisms of thickenings, by gluing the graphs into a single closed subscheme of $X \times_R Y$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated g]
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n)
    (γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n)
    (hγ₁ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n)
    (hγ₂ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g = φ n ≫ adicThickeningι g I n) :
    ∀ n : ℕ, IsClosedImmersion (γ n) ∧
      ((γ (n + 1)).ker).comap (adicThickeningTransition (pullback.fst f g ≫ f) I n) = (γ n).ker := by sorry
