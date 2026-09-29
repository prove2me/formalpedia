-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_valuationSubring_algHom_apply_eq_forall_mem_iff
-- name    : AlgebraicCurve.Place.exists_valuationSubring_algHom_apply_eq_forall_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/4bfb41e0-fb47-5397-b99f-3f3fabd08381
-- title:
--   Realising a prescribed place of M/K under an embedding sending t ↦ j
-- statement:
--   Let $K$ be a field and $M$ a field extension of $K$, let $t \in M$ be transcendental over $K$, and assume $M$ is finite-dimensional and Galois over the intermediate field $K\langle t\rangle = K(t)$. Let $W_0$ be a place of $M$ over $K$, that is, a valuation subring $\mathcal{O}_{W_0}$ of $M$ containing $\operatorname{im}(K \to M)$, different from $M$ itself, and a principal ideal ring; assume $j_0 \in K$ is such that $t - j_0$ is a non-unit of $\mathcal{O}_{W_0}$. Let $\Omega$ be a further extension of $K$ with a place $W$ over $K$ (a valuation subring $\mathcal{O}_W \neq \Omega$ of $\Omega$ containing the image of $K$ and a principal ideal ring), and let $j \in \Omega$ be transcendental over $K$ with $j - j_0$ a non-unit of $\mathcal{O}_W$. Finally let $\Omega'$ be an algebraically closed field which is an extension of $\Omega$ compatibly with $K$ (scalar tower $K \to \Omega \to \Omega'$). The assertion is that there exist a valuation subring $O$ of $\Omega'$ and a $K$-algebra homomorphism $\iota : M \to \Omega'$ such that, for $a \in \Omega$, the image of $a$ in $\Omega'$ lies in $O$ if and only if $a \in \mathcal{O}_W$; such that $\iota(t)$ is the image of $j$ in $\Omega'$; and such that, for $m \in M$, $\iota(m) \in O$ if and only if $m \in \mathcal{O}_{W_0}$.
--
--   This combines Chevalley's extension theorem for valuation rings with the conjugacy of the places of a finite Galois extension above a given place of $K(t)$: the place $W$ of $\Omega$ is extended to a valuation subring of the algebraically closed field $\Omega'$, the specialisation $t \mapsto j$ is extended to a $K$-embedding of $M$, and the embedding is twisted by an element of $\mathrm{Gal}(M/K(t))$ so that the pullback of $O$ along $\iota$ is exactly the prescribed place $W_0$ centred at $t = j_0$. It is used in the treatment of places of modular curves, where it transfers integrality and non-unit statements about the modular $j$-invariant, as in [`ModularCurve.IsModuliPlaceOf.mem_nonunits_iff_of_isIntegral_jModElt`](thm.html#ModularCurve.IsModuliPlaceOf.mem_nonunits_iff_of_isIntegral_jModElt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_valuationSubring_algHom_apply_eq_forall_mem_iff.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField

universe u v w x in

theorem AlgebraicCurve.Place.exists_valuationSubring_algHom_apply_eq_forall_mem_iff
    {K : Type u} [Field K] {M : Type v} [Field M] [Algebra K M]
    (t : M) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
    (W₀ : Place K M) (j₀ : K) (hW₀ : t - algebraMap K M j₀ ∈ W₀.toValuationSubring.nonunits)
    {Ω : Type w} [Field Ω] [Algebra K Ω] (W : Place K Ω) (j : Ω) (hj : Transcendental K j)
    (hjW : j - algebraMap K Ω j₀ ∈ W.toValuationSubring.nonunits)
    (Ω' : Type x) [Field Ω'] [IsAlgClosed Ω'] [Algebra K Ω'] [Algebra Ω Ω']
    [IsScalarTower K Ω Ω'] :
    ∃ (O : ValuationSubring Ω') (ι : M →ₐ[K] Ω'),
      (∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ W.toValuationSubring) ∧
      ι t = algebraMap Ω Ω' j ∧
      ∀ m : M, ι m ∈ O ↔ m ∈ W₀.toValuationSubring := by sorry
