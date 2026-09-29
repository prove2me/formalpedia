-- Prove2me | Theorems.Thm_ArtinL_Abelian_exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq
-- name    : ArtinL.Abelian.exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/73065418-f928-5e01-9d49-95d0fde98372
-- title:
--   Inertia groups at conjugate primes are conjugate
-- statement:
--   Let $K$ and $M$ be number fields with $M$ an algebra over $K$ and $M/K$ Galois, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and let $Q$ be a maximal ideal of $\mathcal{O}_M$ whose contraction to $\mathcal{O}_K$ is the ideal underlying $v$. Then there exists $\tau \in \mathrm{Gal}(M/K)$ with the following properties. First, for every $x \in \mathcal{O}_M$ one has $x \in \mathfrak{P}$ if and only if $\tau \cdot x \in Q$, where $\mathfrak{P} =$ [`LanglandsTunnell.P2.Artin.primeAbove K M v`](def/LanglandsTunnell_ArtinFrobenius.html#L40) is the prime of $\mathcal{O}_M$ chosen once and for all above $v$; equivalently $\tau(\mathfrak{P}) = Q$. Second, for every natural number $i$, writing $G_i =$ [`ArtinL.Abelian.ramificationGroup K M v i`](def/ArtinL_Abelian.html#L25) for the inertia subgroup of $\mathfrak{P}^{i+1}$, that is $\{\sigma : \sigma x - x \in \mathfrak{P}^{i+1} \text{ for all } x \in \mathcal{O}_M\}$: (a) the inertia subgroup of $Q^{i+1}$, namely $\{\sigma : \sigma x - x \in Q^{i+1} \text{ for all } x\}$, equals the image of $G_i$ under conjugation $\sigma \mapsto \tau\sigma\tau^{-1}$; (b) the two subgroups have equal cardinality as naturals; and (c) for every commutative group $A$ and every group homomorphism $\psi : \mathrm{Gal}(M/K) \to A$, $\psi$ is trivial on the inertia subgroup of $Q^{i+1}$ if and only if it is trivial on $G_i$.
--
--   This is the standard transitivity statement that the higher ramification (inertia) groups attached to two primes of $M$ above the same prime of $K$ are conjugate, here in the form needed to pass from the globally chosen prime above $v$ to an arbitrary one. It is used in the computation of Artin and Swan conductors, where the primes chosen in $M$ and in an intermediate field need not be compatible, and it is cited in [`ArtinL.Abelian.finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent`](thm.html#ArtinL.Abelian.finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent) and [`ArtinL.Abelian.swanConductor_comp_restrictNormalHom`](thm.html#ArtinL.Abelian.swanConductor_comp_restrictNormalHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (v : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsMaximal] (hQ : Q.under (𝓞 K) = v.asIdeal) :
    ∃ τ : M ≃ₐ[K] M,
      (∀ x : 𝓞 M, x ∈ LanglandsTunnell.P2.Artin.primeAbove K M v ↔ τ • x ∈ Q) ∧
      ∀ i : ℕ,
        (Q ^ (i + 1)).inertia (M ≃ₐ[K] M) = (ArtinL.Abelian.ramificationGroup K M v i).map (MulAut.conj τ).toMonoidHom ∧
        Nat.card ((Q ^ (i + 1)).inertia (M ≃ₐ[K] M)) = Nat.card (ArtinL.Abelian.ramificationGroup K M v i) ∧
        ∀ {A : Type*} [CommGroup A] (ψ : (M ≃ₐ[K] M) →* A),
          (∀ σ ∈ (Q ^ (i + 1)).inertia (M ≃ₐ[K] M), ψ σ = 1) ↔
            ∀ σ ∈ ArtinL.Abelian.ramificationGroup K M v i, ψ σ = 1 := by sorry
