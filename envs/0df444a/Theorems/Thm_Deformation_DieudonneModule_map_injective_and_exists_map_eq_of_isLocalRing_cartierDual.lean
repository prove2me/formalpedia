-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
-- name    : Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/26a6ef83-665e-5d4e-bbd5-7aae885e058c
-- title:
--   Full faithfulness of the Dieudonné functor over Fₚ
-- statement:
--   Let $p$ be a prime and let $A$ and $B$ be commutative rings equipped with Hopf algebra structures over $\mathbf{F}_p = \mathbb{Z}/p$ whose comultiplications are cocommutative and which are finite as $\mathbf{F}_p$-modules. Assume that the Cartier duals $\mathrm{CartierDual}(\mathbf{F}_p,A)$ and $\mathrm{CartierDual}(\mathbf{F}_p,B)$, i.e. the dual modules $\mathrm{Hom}_{\mathbf{F}_p}(A,\mathbf{F}_p)$ and $\mathrm{Hom}_{\mathbf{F}_p}(B,\mathbf{F}_p)$ with their convolution ring structures, are local rings. Write $M(C) = \mathrm{DieudonneModule}(\mathbf{F}_p,p,C)$ for the direct limit, over $n$, of the additive subgroups $\mathrm{wittHom}$ of $\mathbb{W}_n(C)$ consisting of those truncated Witt vectors $x$ of length $n$ with $\mathbb{W}_n(\Delta)(x) = \mathbb{W}_n(\iota_1)(x) + \mathbb{W}_n(\iota_2)(x)$, where $\Delta$ is the comultiplication and $\iota_1,\iota_2 \colon C \to C \otimes_{\mathbf{F}_p} C$ are the two inclusions, the limit being taken along the maps induced by the Witt-vector shift; $M(C)$ carries the endomorphisms $\mathrm{frobenius}$ and $\mathrm{verschiebung}$ induced levelwise by the Frobenius and Verschiebung of truncated Witt vectors, and every bialgebra homomorphism $\varphi$ induces an additive map $\mathrm{map}$ on these modules by functoriality of Witt vectors. The conclusion is the conjunction of two assertions: first, for bialgebra homomorphisms $g, g' \colon B \to A$ over $\mathbf{F}_p$, equality of the induced additive maps $M(B) \to M(A)$ forces $g = g'$; second, every additive map $\varphi \colon M(B) \to M(A)$ commuting with $\mathrm{frobenius}$ and with $\mathrm{verschiebung}$ is of the form $\mathrm{map}$ of some bialgebra homomorphism $g \colon B \to A$.
--
--   This is the full faithfulness of the contravariant Dieudonné functor on finite commutative group schemes over $\mathbf{F}_p$ whose Cartier duals have local coordinate ring (the unipotent case): bialgebra homomorphisms $B \to A$ correspond exactly to additive maps of Dieudonné modules commuting with $F$ and $V$. It is used in the construction of finite flat group schemes from Dieudonné data and in the base-change and equivalence statements for Dieudonné modules that follow it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A]
    (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B]
    (hA : IsLocalRing (CartierDual (ZMod p) A)) (hB : IsLocalRing (CartierDual (ZMod p) B)) :
    (∀ g g' : B →ₐc[ZMod p] A,
        Deformation.DieudonneModule.map (ZMod p) p g = Deformation.DieudonneModule.map (ZMod p) p g' →
        g = g') ∧
    (∀ φ : Deformation.DieudonneModule (ZMod p) p B →+ Deformation.DieudonneModule (ZMod p) p A,
        (∀ z, φ (Deformation.DieudonneModule.frobenius (ZMod p) p B z) =
          Deformation.DieudonneModule.frobenius (ZMod p) p A (φ z)) →
        (∀ z, φ (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) =
          Deformation.DieudonneModule.verschiebung (ZMod p) p A (φ z)) →
        ∃ g : B →ₐc[ZMod p] A, Deformation.DieudonneModule.map (ZMod p) p g = φ) := by sorry
