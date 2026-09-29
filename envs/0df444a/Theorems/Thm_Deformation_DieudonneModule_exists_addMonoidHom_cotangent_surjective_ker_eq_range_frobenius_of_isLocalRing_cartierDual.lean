-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual
-- name    : Deformation.DieudonneModule.exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/2d6b88f0-dee8-5665-9bbf-5cf661d4fe90
-- title:
--   Dieudonné module modulo Frobenius is the cotangent space
-- statement:
--   Let $p$ be a prime and let $B$ be a commutative ring that is a Hopf algebra over $\mathbb{Z}/p$, with cocommutative comultiplication and finite as a $\mathbb{Z}/p$-module; assume that its Cartier dual [`CartierDual (ZMod p) B`](def/HopfAlgebra_CartierDual.html#L12), namely the $\mathbb{Z}/p$-linear dual of $B$ with its ring structure, is a local ring, and that $B$ itself is a local ring. Write $I = \ker\varepsilon$ for the kernel of the counit algebra map `Bialgebra.counitAlgHom (ZMod p) B`. The assertion is that there is a homomorphism of additive groups $\theta$ from [`Deformation.DieudonneModule (ZMod p) p B`](def/Dieudonne_WittHomColimit.html#L234) — the direct limit, along the shift maps, of the additive subgroups [`Deformation.wittHom (ZMod p) p n B`](def/Dieudonne_WittVectorHom.html#L246) of $W_n(B)$ consisting of truncated Witt vectors $x$ with $W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x)$, where $\Delta$ is the comultiplication and $\iota_1,\iota_2 : B \to B \otimes_{\mathbb{Z}/p} B$ the two inclusions — to the cotangent module $I/I^2$, with three properties: for every $n$ and every $x$ in the level $n+1$ subgroup whose coefficient of index `Fin.last n` lies in $I$, the value of $\theta$ on the image of $x$ in the limit is the class of that last coefficient in $I/I^2$; $\theta$ is surjective; and $\theta(z) = 0$ holds precisely when $z$ lies in the range of the Frobenius endomorphism [`Deformation.DieudonneModule.frobenius (ZMod p) p B`](def/Dieudonne_WittHomColimit.html#L333).
--
--   This is Fontaine's comparison between the Dieudonné module of a finite connected unipotent commutative group scheme over $\mathbb{F}_p$ and its cotangent space at the origin, giving $M(G)/F\,M(G) \cong \mathfrak m/\mathfrak m^2$. It is used in the construction of the Honda system attached to such a group scheme, via [`Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq`](thm.html#Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Deformation.DieudonneModule.exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] (hB : IsLocalRing (CartierDual (ZMod p) B)) (hBloc : IsLocalRing B) :
    ∃ θ : Deformation.DieudonneModule (ZMod p) p B →+
        (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).Cotangent,
      (∀ (n : ℕ) (x : Deformation.wittHom (ZMod p) p (n + 1) B)
          (hx : (x : TruncatedWittVector p (n + 1) B).coeff (Fin.last n) ∈
            RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)),
        θ (Deformation.DieudonneModule.of (ZMod p) p B (n + 1) x) =
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).toCotangent ⟨_, hx⟩) ∧
      Function.Surjective θ ∧
      ∀ z, θ z = 0 ↔ z ∈ (Deformation.DieudonneModule.frobenius (ZMod p) p B).range := by sorry
