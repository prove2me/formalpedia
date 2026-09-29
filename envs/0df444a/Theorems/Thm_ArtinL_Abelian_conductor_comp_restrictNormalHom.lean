-- Prove2me | Theorems.Thm_ArtinL_Abelian_conductor_comp_restrictNormalHom
-- name    : ArtinL.Abelian.conductor_comp_restrictNormalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/7d30c08d-700c-5fb6-9672-987c03e6dbe3
-- title:
--   Inflation invariance of conductor, local values and plus places
-- statement:
--   Let $K \subseteq L \subseteq M$ be number fields, with $M$ an extension of $L$ compatibly over $K$ (a scalar-tower hypothesis), and with both $L/K$ and $M/K$ Galois; let $\psi \colon \mathrm{Gal}(L/K) \to \mathbb{C}^{\times}$ be a group homomorphism into the units of $\mathbb{C}$, and let $\psi' = \psi \circ \mathrm{res}$ be its inflation along the restriction homomorphism $\mathrm{Gal}(M/K) \to \mathrm{Gal}(L/K)$. Three assertions are made. First, the conductors of $\psi'$ and of $\psi$ coincide as ideals of $\mathcal{O}_K$; here the conductor of a character is the finitely supported product over the height-one primes $v$ of $\mathcal{O}_K$ of $v^{e}$, with exponent $e = (1$ if the character is nontrivial on the inertia group at $v$, else $0) + \lceil \mathrm{swanConductor} \rceil$ at $v$. Second, for every height-one prime $v$ of $\mathcal{O}_K$ the local values agree, where the local value of a character at $v$ is its value on the arithmetic Frobenius `artinFrob` at a chosen prime of the upper field above $v$ when the character kills the inertia group at $v$, and $0$ otherwise. Third, for every infinite place $w$ of $K$, $\psi'$ satisfies `IsPlusAt` at $w$ — vanishing, i.e. taking value $1$, on the stabiliser of every place of $M$ restricting to $w$ — if and only if $\psi$ does, with places of $L$ in place of places of $M$.
--
--   This is the invariance under inflation of the Artin conductor, of the Frobenius (local) values and of the behaviour at the real places for a one-dimensional character along a tower of Galois number fields, the conductor part resting on Herbrand's compatibility of the ramification filtration with quotients. It is used in the construction of a narrow ray class character whose conductor and local values match prescribed data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_conductor_comp_restrictNormalHom.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain

universe u v w

theorem ArtinL.Abelian.conductor_comp_restrictNormalHom
    (K : Type u) (L : Type v) (M : Type w) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (ψ : (L ≃ₐ[K] L) →* ℂˣ) :
    ArtinL.Abelian.conductor (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) =
        ArtinL.Abelian.conductor ψ ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        ArtinL.Abelian.localValue (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) v =
          ArtinL.Abelian.localValue ψ v) ∧
      (∀ w : InfinitePlace K,
        ArtinL.Abelian.IsPlusAt (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) w ↔
          ArtinL.Abelian.IsPlusAt ψ w) := by sorry
