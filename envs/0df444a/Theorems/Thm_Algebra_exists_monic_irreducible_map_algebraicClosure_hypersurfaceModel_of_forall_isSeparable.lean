-- Prove2me | Theorems.Thm_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable
-- name    : Algebra.exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/bfe382b6-c67e-5e46-a017-07a673cb5b0e
-- title:
--   Generic absolutely irreducible hypersurface model of a finite-type domain
-- statement:
--   Let $k$ be a field, let $R$ be a domain which is a finitely generated $k$-algebra, and let $C$ be a domain which is a $k$-algebra and a finitely generated $R$-algebra, the two structures being compatible (scalar tower), with $R$ acting faithfully on $C$, i.e. $R \to C$ injective. Write $K$ for the intermediate field $k(\operatorname{im} R)$ of $\operatorname{Frac}(C)$ generated over $k$ by the image of $R$, and assume that every $\theta \in \operatorname{Frac}(C)$ which is separable over $K$ already lies in $K$. Then there exist a nonzero $r \in R$, an integer $d$, elements $z : \mathrm{Fin}\,d \to C$, an element $w \in C$, a polynomial $F \in R[X_1,\dots,X_d][T]$ and a polynomial $g \in R[X_1,\dots,X_d]$ such that: $z$ is algebraically independent over $R$; $F$ is monic in $T$; $F$ vanishes at $w$ after substituting $z$ for the $X_i$ (evaluation through the $R$-algebra map $\mathrm{aeval}\,z$); the image of $F$ under the coefficientwise map $R \to \overline{\operatorname{Frac}(R)}$ is irreducible in $\overline{\operatorname{Frac}(R)}[X_1,\dots,X_d][T]$; $g \neq 0$; for every $c \in C$ there are $m$ and $M > 0$ with $\bigl(g(z)^m c\bigr)^M \in R[z_1,\dots,z_d,w]$; and for every $c \in C$ there is $n$ with $r^n \cdot c$ integral over $R[z_1,\dots,z_d]$.
--
--   This is the relative form of Noether's reduction of an irreducible variety to a birationally equivalent hypersurface, stated over a finitely generated base domain and in arbitrary characteristic, the separable-closedness hypothesis on $K$ in $\operatorname{Frac}(C)$ giving absolute irreducibility of the hypersurface equation and the exponents $M$ accounting for the purely inseparable part. It is used in the proof of [`Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime`](thm.html#Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime), where one needs, generically over $\operatorname{Spec} R$, a finite presentation of $C$ by an absolutely irreducible monic equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Algebra.exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C] [FaithfulSMul R C]
    (hgi : ∀ θ : FractionRing C,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C) (w : C) (F : Polynomial (MvPolynomial (Fin d) R))
      (g : MvPolynomial (Fin d) R),
      AlgebraicIndependent R z ∧ F.Monic ∧
      F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin d) R →ₐ[R] C).toRingHom w = 0 ∧
      Irreducible (F.map (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))))) ∧
      g ≠ 0 ∧
      (∀ c : C, ∃ m M : ℕ, 0 < M ∧
        ((MvPolynomial.aeval z g) ^ m * c) ^ M ∈ Algebra.adjoin R (insert w (Set.range z))) ∧
      (∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c)) := by sorry
