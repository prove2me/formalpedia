-- Prove2me | Theorems.Thm_Algebra_exists_natCard_algHom_fiber_eq_finSepDegree
-- name    : Algebra.exists_natCard_algHom_fiber_eq_finSepDegree
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:46:37.326664+00:00
-- url     : https://prove2.me/theorems/5a1efdc5-76d2-5f13-8255-1758463db907
-- title:
--   Generic fibre count equals the separable degree for a finite extension of domains over an algebraically closed field
-- statement:
--   Let $k$ be an algebraically closed field and let $R \subseteq B$ be integral domains that are $k$-algebras (compatibly: $k \to R \to B$), with $B$ finitely generated as an $R$-module. Let $K = \operatorname{Frac} R$ and $L = \operatorname{Frac} B$, so that $L/K$ is a finite field extension, and let $[L:K]_s$ be its separable degree. For a $k$-point $\chi : R \to k$ (a $k$-algebra homomorphism) write
--
--   $$F(\chi) = \{\, \psi : B \to k \ \text{a } k\text{-algebra homomorphism} \;:\; \psi|_R = \chi \,\}$$
--
--   for the set of $k$-points of $\operatorname{Spec} B$ lying over $\chi$. Then there is a nonzero $a \in R$ such that for every $k$-point $\chi$ of $R$ with $\chi(a) \neq 0$ the fibre $F(\chi)$ is finite and
--
--   $$\# F(\chi) = [L:K]_s.$$
--
--   Geometrically: for a finite dominant morphism $\operatorname{Spec} B \to \operatorname{Spec} R$ of integral affine $k$-schemes, every $k$-point of the dense open set $D(a)$ has exactly $[L:K]_s$ preimages (in characteristic $0$ this is the degree $[L:K]$). Proof sketch: choose a primitive element $\beta \in B$ of the separable closure of $K$ in $L$ and a monic $f_0 \in R[X]$ lifting its minimal polynomial; take $a$ to be a product of a discriminant-type witness making $\chi(f_0)$ separable and denominators $c_b$ with $c_b\, b^{q^{n_b}} \in R[\beta]$ for a finite set of $R$-module generators $b$ of $B$ ($q$ the characteristic exponent). Over $\chi(a) \neq 0$ a point of the fibre is determined by $\psi(\beta)$, which must be a root of $\chi(f_0)$, and every one of its $\deg f_0 = [L:K]_s$ distinct roots occurs (going up).
--
--   Role: the point count of a finite map in terms of the separable degree, used for the degree of an isogeny of abelian varieties.
--
--   **Formalization Note**: the fibre is written inline as the subtype `{ψ : B →ₐ[k] k // ψ.comp (IsScalarTower.toAlgHom k R B) = χ}`; the fraction fields are arbitrary `K`, `L` with `IsFractionRing R K`, `IsFractionRing B L` and the compatible towers `R → K → L`, `R → B → L` (these force $R \to B$ to be injective); the separable degree is `Field.finSepDegree K L`. All types live in one universe `u`. The statement is not vacuous: e.g. $R = B = k[X]$, $K = L = k(X)$ satisfies all hypotheses (then every fibre is a single point and $[L:K]_s = 1$); for $R = k[X^2] \subseteq B = k[X]$ in characteristic $\neq 2$ the fibre over $X^2 \mapsto c$ has the two points $X \mapsto \pm\sqrt c$ when $c \neq 0$.
-- source:
--   I. R. Shafarevich, Basic Algebraic Geometry 1, 3rd ed., Springer (2013), Chapter II, Section 6.3 (degree of a finite map: the number of preimages over a dense open set equals the separable degree); D. Mumford, Abelian Varieties, Section 4 (degree of an isogeny); The Stacks Project, chapter Varieties (generic number of points of a finite dominant morphism)

import Mathlib

set_option autoImplicit false

universe u

theorem Algebra.exists_natCard_algHom_fiber_eq_finSepDegree
    (k R B K L : Type u) [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] [Module.Finite R B]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R B L] :
    ∃ a : R, a ≠ 0 ∧ ∀ χ : R →ₐ[k] k, χ a ≠ 0 →
      Finite {ψ : B →ₐ[k] k // ψ.comp (IsScalarTower.toAlgHom k R B) = χ} ∧
      Nat.card {ψ : B →ₐ[k] k // ψ.comp (IsScalarTower.toAlgHom k R B) = χ} =
        Field.finSepDegree K L := by
  sorry
