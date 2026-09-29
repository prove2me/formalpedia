-- Prove2me | Theorems.Thm_Bialgebra_exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom
-- name    : Bialgebra.exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/74dd22f8-98aa-56d5-aaa5-6e4e5fd5604f
-- title:
--   Tangent vectors at the counit as linear forms on I/I²
-- statement:
--   Let $k$ be a commutative ring and let $B$ be a commutative ring carrying a $k$-bialgebra structure, with counit $\varepsilon =$ `Bialgebra.counitAlgHom k B` $\colon B \to k$ and augmentation ideal $I = \ker\varepsilon$; write $k[\epsilon] =$ `DualNumber k` $=$ `TrivSqZeroExt k k` for the dual numbers, with components `fst` and `snd`, and $I.\mathrm{Cotangent}$ for the Mathlib cotangent module $I/I^2$ of the ideal $I$, viewed as a $k$-module. The assertion is that there exists a bijection $\gamma$ between the set of $k$-algebra homomorphisms $D \colon B \to k[\epsilon]$ satisfying $\mathrm{fst}(D b) = \varepsilon(b)$ for all $b \in B$, and the $k$-linear forms $I/I^2 \to k$, with two properties. First, for every such $D$ and every $x \in I$, the value of $\gamma(D)$ on the class `toCotangent` $x$ of $x$ in $I/I^2$ is $\mathrm{snd}(D x)$, the $\epsilon$-component of $D(x)$. Second, $\gamma$ is functorial: for every $k$-algebra homomorphism $q \colon B \to B$ with $I \subseteq q^{-1}(I)$ and all $D, D'$ in that set with $D'(b) = D(q(b))$ for all $b \in B$, one has $\gamma(D') = \gamma(D) \circ \bar q$, where $\bar q \colon I/I^2 \to I/I^2$ is the map `mapCotangent` induced by $q$.
--
--   This is the standard identification of the tangent space at the unit section of the affine monoid scheme $\operatorname{Spec} B$ — tangent vectors being $k$-points of $B$ valued in dual numbers lying over the counit — with the $k$-dual of the cotangent module $I/I^2$ of the augmentation ideal, stated over an arbitrary commutative base ring and together with its compatibility with endomorphisms of $B$ preserving the augmentation ideal. It is used in the analysis of the cotangent module of a model of a modular curve at the cusp, where the functoriality in $q$ transports the action of an endomorphism to the induced map on cotangent spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Bialgebra.exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom
    (k : Type*) [CommRing k] (B : Type*) [CommRing B] [Bialgebra k B] :
    ∃ γ : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b} ≃
        ((RingHom.ker (Bialgebra.counitAlgHom k B)).Cotangent →ₗ[k] k),
      (∀ (D : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b})
          (x : ↥(RingHom.ker (Bialgebra.counitAlgHom k B))),
          γ D ((RingHom.ker (Bialgebra.counitAlgHom k B)).toCotangent x) =
            TrivSqZeroExt.snd (D.1 (x : B))) ∧
      (∀ (q : B →ₐ[k] B)
          (hq : RingHom.ker (Bialgebra.counitAlgHom k B) ≤
            (RingHom.ker (Bialgebra.counitAlgHom k B)).comap q)
          (D D' : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b}),
          (∀ b : B, D'.1 b = D.1 (q b)) →
          γ D' = γ D ∘ₗ
            (RingHom.ker (Bialgebra.counitAlgHom k B)).mapCotangent
              (RingHom.ker (Bialgebra.counitAlgHom k B)) q hq) := by sorry
