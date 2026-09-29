-- Prove2me | Theorems.Thm_CuspidalType_finsupp_apply_pow_eq_of_forall_character_torus_eq_sum
-- name    : CuspidalType.finsupp_apply_pow_eq_of_forall_character_torus_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/188f9d46-4702-514e-8b24-8c3428a0d466
-- title:
--   Frobenius invariance of torus character multiplicities
-- statement:
--   Let $q$ be a prime, let $K$ be an algebraically closed field of characteristic zero, and let $V$ be a nontrivial finite-dimensional $K$-vector space. Write $\mathrm{GL2}\,q$ for $\mathrm{GL}_2(\mathbb{Z}/q)$ and, for a unit $\alpha$ of the field $\mathrm{GaloisField}\,q\,2$ with $q^2$ elements, let $\mathrm{torus}\,q\,\alpha \in \mathrm{GL}_2(\mathbb{Z}/q)$ be the matrix of multiplication by $\alpha$ on $\mathrm{GaloisField}\,q\,2$, taken with respect to the two-element $\mathbb{Z}/q$-basis `quadBasis` coming from $\dim_{\mathbb{Z}/q}\mathrm{GaloisField}\,q\,2 = 2$; this is a monoid homomorphism on units. Given a representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V$ over $K$, a finitely supported function $m$ from the character group $\mathrm{Hom}((\mathrm{GaloisField}\,q\,2)^{\times}, K^{\times})$ to $\mathbb{N}$, and the hypothesis that for every $\alpha$ the character value $\rho.\mathrm{character}(\mathrm{torus}\,q\,\alpha)$ equals the finite sum $\sum_{\mu} m(\mu)\,\mu(\alpha)$ over the support of $m$ (the multiplicities being taken in $K$ via $\mathbb{N} \to K$), the conclusion is that for every character $\mu$ one has $m(\mu^{q}) = m(\mu)$, where $\mu^q$ is the $q$-th power in the character group.
--
--   This is the statement that in the character expansion of a representation of $\mathrm{GL}_2(\mathbb{F}_q)$ restricted to a nonsplit torus $\mathbb{F}_{q^2}^{\times}$, the multiplicity function is invariant under the Frobenius twist $\mu \mapsto \mu^q$, reflecting $\pi_\theta \cong \pi_{\theta^q}$ in the character theory of $\mathrm{GL}_2$ over a finite field. It is used in the analysis of representations of cuspidal type, feeding into [`CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq`](thm.html#CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_finsupp_apply_pow_eq_of_forall_character_torus_eq_sum.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.finsupp_apply_pow_eq_of_forall_character_torus_eq_sum
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    [Fintype (GaloisField q 2)ˣ] (ρ : Representation K (GL2 q) V)
    (m : ((GaloisField q 2)ˣ →* Kˣ) →₀ ℕ)
    (htr : ∀ α, ρ.character (torus q α) = m.sum fun μ n => (n : K) * ((μ α : Kˣ) : K)) (μ : (GaloisField q 2)ˣ →* Kˣ) :
    m (μ ^ q) = m μ := by sorry
