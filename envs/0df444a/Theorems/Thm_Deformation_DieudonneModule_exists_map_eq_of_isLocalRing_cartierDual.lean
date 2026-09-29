-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual
-- name    : Deformation.DieudonneModule.exists_map_eq_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/d1cd4bc7-af2a-5be1-8f9f-9310254d9b9f
-- title:
--   Fullness of the Dieudonné module functor over 𝔽ₚ
-- statement:
--   Let $p$ be a prime, and let $A$ be a commutative ring carrying a bialgebra structure over $\mathbb{Z}/p$ and finite as a $\mathbb{Z}/p$-module, and let $B$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}/p$ whose comultiplication is cocommutative, again finite over $\mathbb{Z}/p$. Assume that [`CartierDual (ZMod p) B`](def/HopfAlgebra_CartierDual.html#L12), the $\mathbb{Z}/p$-linear dual $\mathrm{Hom}_{\mathbb{Z}/p}(B,\mathbb{Z}/p)$ with its ring structure, is a local ring. Here [`Deformation.DieudonneModule (ZMod p) p C`](def/Dieudonne_WittHomColimit.html#L234) denotes the direct limit, along the maps induced by the Verschiebung-type embeddings $W_n \to W_{n+1}$, of the additive subgroups [`Deformation.wittHom`](def/Dieudonne_WittVectorHom.html#L246) of $W_n(C)$ consisting of those truncated Witt vectors $x$ with $W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x)$; it carries the additive endomorphisms `frobenius` (levelwise coordinatewise $p$-th power) and `verschiebung`. Let $\varphi$ be a homomorphism of additive groups from the Dieudonné module of $B$ to that of $A$ commuting with `frobenius` and with `verschiebung`. Then there is a morphism $g : B \to A$ of $\mathbb{Z}/p$-bialgebras (an algebra map that is also a coalgebra map) whose induced additive map [`Deformation.DieudonneModule.map (ZMod p) p g`](def/Dieudonne_WittHomColimit.html#L380), given levelwise by $x \mapsto W_n(g)(x)$, equals $\varphi$.
--
--   This is the fullness half of the classical Dieudonné correspondence for unipotent finite commutative group schemes over $\mathbb{F}_p$ (Demazure–Gabriel V §1, Thm. 4.3), the locality of the Cartier dual expressing unipotence of $\operatorname{Spec} B$. It is combined with the corresponding injectivity statements in [`Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual`](thm.html#Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual) and [`Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual`](thm.html#Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual) to give full faithfulness of the Dieudonné module functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneModule.exists_map_eq_of_isLocalRing_cartierDual
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Bialgebra (ZMod p) A] [Module.Finite (ZMod p) A]
    (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B]
    (hB : IsLocalRing (CartierDual (ZMod p) B))
    (φ : Deformation.DieudonneModule (ZMod p) p B →+ Deformation.DieudonneModule (ZMod p) p A)
    (hF : ∀ z, φ (Deformation.DieudonneModule.frobenius (ZMod p) p B z) =
      Deformation.DieudonneModule.frobenius (ZMod p) p A (φ z))
    (hV : ∀ z, φ (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p A (φ z)) :
    ∃ g : B →ₐc[ZMod p] A, Deformation.DieudonneModule.map (ZMod p) p g = φ := by sorry
