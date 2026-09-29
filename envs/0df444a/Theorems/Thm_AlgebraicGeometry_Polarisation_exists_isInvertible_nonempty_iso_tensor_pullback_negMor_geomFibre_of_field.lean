-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field
-- name    : AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/8272f351-5009-5562-af6b-d4e7bdcff2c5
-- title:
--   Descent of a square root of L to a geometric fibre
-- statement:
--   Let $S$ be a commutative ring and $f : A \to \operatorname{Spec} S$ a morphism of schemes, equipped with a relative group law $L$ in the sense of the project: a functorial group structure on the sets of $T$-points over $\operatorname{Spec} S$, given by operations `mul`, `one`, `inv` on $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for each $t : T \to \operatorname{Spec} S$, satisfying associativity, the two unit laws, left inversion, and naturality of multiplication in $T$. Assume the bundle `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth, proper, each fibre $f^{-1}(s)$ is connected, and a relative group law exists. Let $\mathcal L$ be a module on $A$ which is invertible in the project's sense (every point has a neighbourhood $U$ over which the restriction of $\mathcal L$ is isomorphic to the unit module of $U$). Let $k$ be an algebraically closed field with a ring homomorphism $s_k : S \to k$, let $K$ be a field with $s_K : S \to K$, and let $\iota : k \to K$ satisfy $\iota \circ s_k = s_K$. Write $A_K$ and $A_k$ for the fibre products of $f$ with $\operatorname{Spec}$ of $s_K$, resp. $s_k$, and let $[-1]$ denote `negMor` for the base-changed group law, namely the underlying morphism of the inverse of the identity point. Given an invertible module $\mathcal L_0$ on $A_K$ together with an isomorphism (asserted as a nonempty type of isomorphisms) between the pullback of $\mathcal L$ along the first projection $A_K \to A$ and $\mathcal L_0 \otimes [-1]^{*}\mathcal L_0$, the conclusion is that there exists an invertible module $\mathcal L_1$ on $A_k$ and an isomorphism between the pullback of $\mathcal L$ along the first projection $A_k \to A$ and $\mathcal L_1 \otimes [-1]^{*}\mathcal L_1$, for the group law base-changed along $s_k$.
--
--   This is the field-descent step in the construction of a square root of a line bundle on an abelian scheme: a factorisation $\mathcal L \cong \mathcal L_1 \otimes [-1]^{*}\mathcal L_1$ available after an arbitrary field extension of a geometric point is brought back to the geometric fibre itself. It is used by [`AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_exists_faithfullyFlat`](thm.html#AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_exists_faithfullyFlat) in the development of polarisations and the Rosati involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hA : AbelianSchemePropertyBundle S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (K : Type) [Field K] (sK : S →+* K) (ι : k →+* K) (hι : ι.comp sk = sK)
    (𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom sK))).Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (e : Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sK)))).obj 𝓛 ≅
      𝓛₀ ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom sK))) (L.baseChange (Spec.map (CommRingCat.ofHom sK))))).obj 𝓛₀)) :
    ∃ 𝓛₁ : (pullback f (Spec.map (CommRingCat.ofHom sk))).Modules,
      Scheme.Modules.IsInvertible 𝓛₁ ∧
      Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓛 ≅
        𝓛₁ ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) (L.baseChange (Spec.map (CommRingCat.ofHom sk))))).obj 𝓛₁) := by sorry
