-- Prove2me | Theorems.Thm_ArtinL_Abelian_swanConductor_comp_restrictNormalHom
-- name    : ArtinL.Abelian.swanConductor_comp_restrictNormalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/0404a334-a6cd-5af6-ad95-c78cdf544e09
-- title:
--   Inflation invariance of the Swan conductor (Herbrand)
-- statement:
--   Let $K$, $L$, $M$ be number fields (fields with the number-field structure), equipped with $K$-algebra structures on $L$ and $M$ and an $L$-algebra structure on $M$ forming a scalar tower over $K$, and assume both $L/K$ and $M/K$ are Galois. Let $\psi : (L \simeq_{\mathrm{alg}[K]} L) \to \mathbb{C}^\times$ be a homomorphism of the Galois group of $L/K$ into the units of $\mathbb{C}$, and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$. Here [`ArtinL.Abelian.swanConductor`](def/ArtinL_Abelian.html#L49) of a character $\chi$ of $\mathrm{Gal}(F/K)$ at $v$ is the rational number $\sum_{i \ge 0}^{\mathrm{f}} \frac{|\,(\mathfrak{P}^{i+2}).\mathrm{inertia}\,|}{|\,\mathfrak{P}.\mathrm{inertia}\,|} \cdot [\,\chi \not\equiv 1 \text{ on } (\mathfrak{P}^{i+2}).\mathrm{inertia}\,]$, the finite-support sum over $i : \mathbb{N}$ of the indices of the higher inertia subgroups attached to the chosen prime $\mathfrak{P} =$ `primeAbove` $K$ $F$ $v$ of $\mathcal{O}_F$ above $v$, weighted by $0$ or $1$ according as $\chi$ is trivial or not on that subgroup; in classical notation $\sum_{i \ge 1} \frac{|G_i|}{|G_0|}[\psi|_{G_i} \neq 1]$. The assertion is that the Swan conductor at $v$ of the inflation $\psi \circ \mathrm{res}$, where $\mathrm{res} =$ `AlgEquiv.restrictNormalHom` is restriction $\mathrm{Gal}(M/K) \to \mathrm{Gal}(L/K)$, computed with the ramification filtration of $M$, equals the Swan conductor at $v$ of $\psi$ itself, computed with the ramification filtration of $L$.
--
--   This is the wild part of the invariance of the Artin conductor of a one-dimensional character under inflation along a tower $K \subseteq L \subseteq M$ of Galois extensions, resting on Herbrand's compatibility of the ramification filtration with passage to a quotient, together with the conjugacy of the primes above $v$. It is used to deduce the corresponding invariance for the full conductor in [`ArtinL.Abelian.conductor_comp_restrictNormalHom`](thm.html#ArtinL.Abelian.conductor_comp_restrictNormalHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_swanConductor_comp_restrictNormalHom.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain

universe u v w

theorem ArtinL.Abelian.swanConductor_comp_restrictNormalHom
    (K : Type u) (L : Type v) (M : Type w) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (ψ : (L ≃ₐ[K] L) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ArtinL.Abelian.swanConductor (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) v =
      ArtinL.Abelian.swanConductor ψ v := by sorry
