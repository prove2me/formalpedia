-- Prove2me | Theorems.Thm_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic
-- name    : FinFlatHopf.exists_subgroup_inertia_trivial_quotient_cyclotomic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/5888f5ff-3091-5daf-80cd-25ed3c829993
-- title:
--   Inertia acts multiplicatively on a subgroup with unramified quotient
-- statement:
--   Let $p$ be a prime and let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $P$; write $I_P$ for the inertia subgroup of $P$ over $\mathbb{Q}$, viewed inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ as the image of the inertia subgroup of the decomposition subgroup under inclusion. Let $H$ be a commutative ring which is a cocommutative Hopf algebra over the subring $\mathbb{Z}_{(p)}=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$, and which is finite and flat as a $\mathbb{Z}_{(p)}$-module. Let $M$ be an additive abelian group carrying a distributive action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and let $e$ be a bijection from the set of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$, equipped with the convolution monoid structure, onto $M$, such that $e(f\cdot g)=e(f)+e(g)$, and such that whenever $g$ is the pointwise composite $\sigma \circ f$ one has $e(g)=\sigma \cdot e(f)$. Suppose further that $M$ is a module over a commutative local ring $R$ whose residue field has exactly $p$ elements, and that there is a function $u$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $R^\times$ with $\sigma \cdot m = u(\sigma)\, m$ for all $\sigma \in I_P$ and all $m \in M$. Then there exists an additive subgroup $T \le M$ such that: $T$ is stable under $I_P$; $\sigma \cdot m - m \in T$ for every $\sigma \in I_P$ and every $m \in M$; and for all natural numbers $n, a$ and every $\sigma \in I_P$ which satisfies $\sigma(\mu)=\mu^{a}$ for every $\mu \in \overline{\mathbb{Q}}$ with $\mu^{p^{n}}=1$, if $p^{n}$ annihilates $T$ then $\sigma \cdot t = a\,t$ for all $t \in T$.
--
--   This is the multiplicative–étale dichotomy for the inertia action on the $\overline{\mathbb{Q}}$-points of a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$ in the case of scalars with residue field of prime order: the subgroup $T$ plays the role of the points of the multiplicative part, on which inertia acts through the cyclotomic character in its level-$p^{n}$ form, while inertia acts trivially on $M/T$. It is used in the analysis of the local behaviour at $p$ of a flat model, in [`RibetIrr.line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt`](thm.html#RibetIrr.line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FinFlatHopf.exists_subgroup_inertia_trivial_quotient_cyclotomic (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (R : Type) [CommRing R] [IsLocalRing R] [Module R M]
    (hR : Nat.card (IsLocalRing.ResidueField R) = p)
    (u : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hu : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ m : M, σ • m = (u σ : R) • m) :
    ∃ T : AddSubgroup M,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ t ∈ T, σ • t ∈ T) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ m : M, σ • m - m ∈ T) ∧
      ∀ (n a : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        σ ∈ P.inertiaSubgroupIn ℚ →
        (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
        (∀ t ∈ T, p ^ n • t = 0) → ∀ t ∈ T, σ • t = a • t := by sorry
