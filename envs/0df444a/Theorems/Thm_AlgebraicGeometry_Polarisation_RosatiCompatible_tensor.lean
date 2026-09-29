-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_tensor
-- name    : AlgebraicGeometry.Polarisation.RosatiCompatible.tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/405a0ec4-34a3-5587-8105-ced63c0bc08a
-- title:
--   Rosati compatibility passes to tensor products of line bundles
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law on $f$: for every $S$-scheme $t : T \to \operatorname{Spec} S$ a multiplication, unit and inverse on the set of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, satisfying associativity, both unit laws, the left inverse law, and naturality of the multiplication under base change along any $\psi : T' \to T$ over $\operatorname{Spec} S$. Let $I$ be a type, $\mathrm{act} : I \to (A \to A)$ a family of endomorphisms of $A$ with $\mathrm{act}(x)$ followed by $f$ equal to $f$ for each $x$, and $\mathrm{star} : I \to I$ an involution-like index map. Let $\mathcal L, \mathcal L'$ be objects of `A.Modules`, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the restriction along $U.\iota$ is isomorphic to the unit module. Write $\Lambda(\mathcal M) = m^*\mathcal M \otimes (q_1^*\mathcal M^\vee \otimes q_2^*\mathcal M^\vee)$ for the Mumford bundle on $A \times_{\operatorname{Spec} S} A$, with $m$ the addition morphism attached to $L$ and $q_1, q_2$ the two projections. Assume that both $\mathcal L$ and $\mathcal L'$ are Rosati compatible, i.e. for each $b \in I$ the pullbacks of $\Lambda(\mathcal L)$ (resp. $\Lambda(\mathcal L')$) along $(q_1, q_2 \circ \mathrm{act}(b))$ and along $(q_1 \circ \mathrm{act}(\mathrm{star}(b)), q_2)$ are locally isomorphic over the base: every point $s$ of $\operatorname{Spec} S$ has an open neighbourhood $U$ such that the two pullbacks become isomorphic after restriction to the preimage of $U$ under $q_1$ followed by $f$. Then $\mathcal L \otimes \mathcal L'$ is Rosati compatible for the same data.
--
--   This is the multiplicativity of the Rosati-compatibility condition in the line bundle, reflecting the fact that the Mumford bundle construction $\mathcal L \mapsto \Lambda(\mathcal L)$ is monoidal on invertible sheaves. It is used in the construction of canonical polarisation data on the quaternionic side of the Čerednik–Drinfeld uniformisation, where compatible bundles are built by tensoring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_tensor.lean

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

theorem AlgebraicGeometry.Polarisation.RosatiCompatible.tensor
    {S : Type} [CommRing S] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝓛 𝓛' : A.Modules) (h : Scheme.Modules.IsInvertible 𝓛) (h' : Scheme.Modules.IsInvertible 𝓛')
    (hR : RosatiCompatible f L 𝓛 act act_over star) (hR' : RosatiCompatible f L 𝓛' act act_over star) :
    RosatiCompatible f L (𝓛 ⊗ 𝓛') act act_over star := by sorry
