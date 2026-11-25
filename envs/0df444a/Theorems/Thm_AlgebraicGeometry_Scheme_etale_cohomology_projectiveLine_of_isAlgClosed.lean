-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_etale_cohomology_projectiveLine_of_isAlgClosed
-- name    : AlgebraicGeometry.Scheme.etale_cohomology_projectiveLine_of_isAlgClosed
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-25T00:59:59.840619+00:00
-- url     : https://prove2.me/theorems/7f366c39-a059-4604-aa2b-05cd176e43d7
-- title:
--   Étale cohomology of the projective line over an algebraically closed field: $H^1 = 0$, $H^2 \cong \Lambda$ and $H^q = 0$ for $q \ge 3$
-- statement:
--   Let $k$ be an algebraically closed field, let $\mathbb{P}^1_k = \operatorname{Proj} k[X_0, X_1]$ be the projective line over $k$, and let $\Lambda$ be a commutative ring. For a sheaf $F$ of $\Lambda$-modules on the small étale site of $\mathbb{P}^1_k$ write
--
--   $$H^q(\mathbb{P}^1_k, F) = \operatorname{Ext}^q(\underline{\Lambda}, F),$$
--
--   the Ext group in the abelian category of étale sheaves of $\Lambda$-modules, where $\underline{\Lambda}$ is the constant sheaf with value $\Lambda$; this is the étale cohomology of $F$. Write $H^q(\mathbb{P}^1_k, \Lambda)$ for $H^q(\mathbb{P}^1_k, \underline{\Lambda})$. Then:
--
--   1. If $N$ is a natural number that is nonzero in $k$ and $N \cdot \Lambda = 0$, then $H^1(\mathbb{P}^1_k, \Lambda) = 0$.
--   2. If $\ell$ is a prime different from the characteristic of $k$, $n \ge 1$ and $\ell^n \cdot \Lambda = 0$, then $H^2(\mathbb{P}^1_k, \Lambda) \cong \Lambda$ as abelian groups.
--   3. If $\ell$ is a prime different from the characteristic of $k$ and $\ell^m \cdot \Lambda = 0$ for some $m \ge 0$, then $H^q(\mathbb{P}^1_k, F) = 0$ for every $q \ge 3$ and EVERY étale sheaf $F$ of $\Lambda$-modules on $\mathbb{P}^1_k$.
--
--   Together with $H^0(\mathbb{P}^1_k, \Lambda) = \Lambda$, parts 1 and 2 compute the étale cohomology of the projective line with constant torsion coefficients: for $\Lambda = \mathbb{Z}/\ell^n$ one gets $H^*(\mathbb{P}^1_k, \mathbb{Z}/\ell^n) = \mathbb{Z}/\ell^n$ in degrees $0$ and $2$ and $0$ otherwise, the same answer as for a 2-sphere. Part 1 comes from the Kummer sequence: since $\operatorname{Pic} \mathbb{P}^1_k = \mathbb{Z}$ is torsion-free and the global units $k^\times$ are divisible, $H^1(\mathbb{P}^1_k, \mu_N) = 0$, and $\mu_N \cong \mathbb{Z}/N$ because $k$ is algebraically closed. Part 2 comes from the Mayer-Vietoris sequence of the two standard affine charts $U, V \cong \mathbb{A}^1_k$, which meet in $\mathbb{G}_{m,k}$: since $H^1(\mathbb{A}^1_k, \Lambda) = H^2(\mathbb{A}^1_k, \Lambda) = 0$, the connecting map gives $H^2(\mathbb{P}^1_k, \Lambda) \cong H^1(\mathbb{G}_{m,k}, \Lambda) \cong \Lambda$ (the canonical form is $H^2(\mathbb{P}^1_k, \mu_{\ell^n}) \cong \mathbb{Z}/\ell^n$, the degree map; here the isomorphism depends on a choice of roots of unity). Part 3 says that the $\ell$-cohomological dimension of $\mathbb{P}^1_k$ is at most $2$, which is sharp by part 2.
--
--   **Formalization Note**: $\mathbb{P}^1_k$ is `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)`, the projective spectrum of the polynomial ring $k[X_0, X_1]$ graded by total degree (the grading `MvPolynomial.gradedAlgebra` is made a local instance in the preamble). Étale sheaves of $\Lambda$-modules are `CategoryTheory.Sheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology (ModuleCat.{0} Λ)`, $\underline{\Lambda}$ is `(CategoryTheory.constantSheaf _ (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)`, and $H^q(\mathbb{P}^1_k, F)$ is `CategoryTheory.Abelian.Ext` $(\underline{\Lambda}, F, q)$ with values in `Type`, for the `HasExt` structure that Mathlib provides on this Grothendieck abelian category. The hypotheses are `(N : k) ≠ 0` and `(N : Λ) = 0` in part 1; `l.Prime`, `0 < n`, `(l : k) ≠ 0` and `((l ^ n : ℕ) : Λ) = 0` in part 2; `l.Prime`, `(l : k) ≠ 0` and `((l ^ m : ℕ) : Λ) = 0` in part 3. Part 1 is stated as `Subsingleton` of the Ext group in degree 1, part 2 as `Nonempty (Ext^2 ≃+ Λ)` (an isomorphism of additive groups, for Mathlib's `AddCommGroup` structure on `Ext`), and part 3 as `e = 0` for every `e` in degree $n + 3$. $k$ and $\Lambda$ live in `Type`. The statement is not vacuous: for example $k$ the algebraic closure of $\mathbb{Q}$ and $\Lambda = \mathbb{Z}/\ell$ with $N = \ell$ and $n = m = 1$, where part 2 says $H^2(\mathbb{P}^1_k, \mathbb{Z}/\ell) \cong \mathbb{Z}/\ell \ne 0$.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V §2 (the cohomology of curves) and Chapter VI §1 (cohomological dimension); P. Deligne, SGA 4½, Cohomologie étale (Arcata), cohomology of curves

import Mathlib

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.etale_cohomology_projectiveLine_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] (Λ : Type) [CommRing Λ] :
    (∀ N : ℕ, (N : k) ≠ 0 → (N : Λ) = 0 →
      Subsingleton (CategoryTheory.Abelian.Ext
        ((CategoryTheory.constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ))
        ((CategoryTheory.constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) 1 : Type)) ∧
    (∀ l n : ℕ, l.Prime → 0 < n → (l : k) ≠ 0 → ((l ^ n : ℕ) : Λ) = 0 →
      Nonempty ((CategoryTheory.Abelian.Ext
        ((CategoryTheory.constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ))
        ((CategoryTheory.constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) 2 : Type) ≃+ Λ)) ∧
    (∀ l m : ℕ, l.Prime → (l : k) ≠ 0 → ((l ^ m : ℕ) : Λ) = 0 →
      ∀ (F : CategoryTheory.Sheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
          (ModuleCat.{0} Λ)) (n : ℕ)
        (e : (CategoryTheory.Abelian.Ext
          ((CategoryTheory.constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
            (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) F (n + 3) : Type)), e = 0) := by
  sorry
