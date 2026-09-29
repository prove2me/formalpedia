-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_tensor_pullback_negMor_pos_of_commRing
-- name    : AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_pullback_negMor_pos_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/6045cee9-84ac-5bd9-b6ea-4a20c96c9324
-- title:
--   Fibrewise positivity of mathcal L₀ ⊗ [-1]^*mathcal L₀ over a general base
-- statement:
--   Let $S$ be a commutative ring and let $f\colon A \to \operatorname{Spec} S$ be a morphism of schemes equipped with a `RelativeGroupLaw` $L$, i.e. a group structure on the sets of $T$-points of $A$ over $\operatorname{Spec} S$, functorial in $T$ (multiplication, unit and inversion satisfying associativity, both unit laws, left inverses, and naturality of multiplication under change of $T$). Assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, proper, each set-theoretic fibre of the underlying map of $f$ is connected, and $f$ admits a relative group law. Let $\mathcal L_0$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the pullback of $\mathcal L_0$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of $U$. Assume further that for every algebraically closed field $k''$ and every ring homomorphism $S \to k''$ the invariant `Scheme.Modules.geomFibreH0Finrank` of $\mathcal L_0$ — the $k''$-dimension of the global sections of the pullback of $\mathcal L_0$ along the first projection $A \times_{\operatorname{Spec} S} \operatorname{Spec} k'' \to A$ — is positive. Then, for a given algebraically closed field $k'$ and ring homomorphism $sk\colon S \to k'$, the same invariant is positive for $\mathcal L_0 \otimes (\text{negMor } f\, L)^* \mathcal L_0$, where $\text{negMor } f\, L$ is the morphism $A \to A$ underlying the $L$-inverse of the identity point of $A$ over $f$.
--
--   The symmetrisation $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ of a fibrewise effective invertible sheaf on an abelian scheme is again fibrewise effective; this is the general-base form of the corresponding statement over a field. It feeds the construction of canonical polarisation data on the abelian schemes arising in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_tensor_pullback_negMor_pos_of_commRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_pullback_negMor_pos_of_commRing
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hA : AbelianSchemePropertyBundle S f)
    (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hpos : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : S →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛₀ k' sk)
    (k' : Type) [Field k'] [IsAlgClosed k'] (sk : S →+* k') :
    0 < Scheme.Modules.geomFibreH0Finrank f (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) k' sk := by sorry
