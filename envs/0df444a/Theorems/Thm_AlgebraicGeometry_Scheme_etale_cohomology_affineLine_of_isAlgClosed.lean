-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_etale_cohomology_affineLine_of_isAlgClosed
-- name    : AlgebraicGeometry.Scheme.etale_cohomology_affineLine_of_isAlgClosed
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-24T23:04:06.966908+00:00
-- url     : https://prove2.me/theorems/0a485bf0-0df2-4ddc-b68a-4b19ef8cfe13
-- title:
--   Étale cohomology of the affine line over an algebraically closed field: $H^q(\mathbb{A}^1_k, \Lambda) = 0$ for $q \ge 1$ and $H^q(\mathbb{A}^1_k, F) = 0$ for $q \ge 3$
-- statement:
--   Let $k$ be an algebraically closed field, let $\mathbb{A}^1_k = \operatorname{Spec} k[X]$ be the affine line over $k$, and let $\Lambda$ be a commutative ring. For a sheaf $F$ of $\Lambda$-modules on the small étale site of $\mathbb{A}^1_k$ write
--
--   $$H^q(\mathbb{A}^1_k, F) = \operatorname{Ext}^q(\underline{\Lambda}, F),$$
--
--   the Ext group in the abelian category of étale sheaves of $\Lambda$-modules, where $\underline{\Lambda}$ is the constant sheaf with value $\Lambda$; this is the étale cohomology of $F$. Write $H^q(\mathbb{A}^1_k, \Lambda)$ for $H^q(\mathbb{A}^1_k, \underline{\Lambda})$. Then:
--
--   1. If $N$ is a natural number that is invertible in $k$ and $N \cdot \Lambda = 0$, then $H^1(\mathbb{A}^1_k, \Lambda) = 0$.
--   2. If $\ell$ is a prime different from the characteristic of $k$ and $\ell^m \cdot \Lambda = 0$ for some $m \ge 0$, then $H^q(\mathbb{A}^1_k, \Lambda) = 0$ for every $q \ge 2$.
--   3. Under the hypothesis of 2, $H^q(\mathbb{A}^1_k, F) = 0$ for every $q \ge 3$ and EVERY étale sheaf $F$ of $\Lambda$-modules on $\mathbb{A}^1_k$.
--
--   Together with $H^0(\mathbb{A}^1_k, \Lambda) = \Lambda$, parts 1 and 2 say that the affine line over an algebraically closed field is acyclic for constant coefficients killed by a power of a prime $\ell \ne \operatorname{char} k$ (for $\Lambda = \mathbb{Z}/\ell^m$: $H^*(\mathbb{A}^1_k, \mathbb{Z}/\ell^m) = \mathbb{Z}/\ell^m$ in degree $0$ and $0$ otherwise). Part 1 says that $\mathbb{A}^1_k$ has no nontrivial étale cyclic covers of degree dividing $N$; the hypothesis on $N$ is needed, since in characteristic $p > 0$ the Artin–Schreier covers $y^p - y = f(X)$ give $H^1(\mathbb{A}^1_k, \mathbb{Z}/p) \ne 0$. Part 3 bounds the $\ell$-cohomological dimension of $\mathbb{A}^1_k$ by $2$; the sharp bound $1$ (Artin's affine vanishing theorem) is not claimed here. These are the basic computations behind the étale cohomology of curves, for instance of the projective line $\mathbb{P}^1_k$, which is covered by two affine lines.
--
--   **Formalization Note**: $\mathbb{A}^1_k$ is `Spec (CommRingCat.of (Polynomial k))`. Étale sheaves of $\Lambda$-modules are `CategoryTheory.Sheaf (Spec (CommRingCat.of (Polynomial k))).smallEtaleTopology (ModuleCat.{0} Λ)`, $\underline{\Lambda}$ is `(CategoryTheory.constantSheaf _ (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)`, and $H^q(\mathbb{A}^1_k, F)$ is `CategoryTheory.Abelian.Ext` $(\underline{\Lambda}, F, q)$ with values in `Type`, for the `HasExt` structure that Mathlib provides on this Grothendieck abelian category. "$N$ invertible in $k$" is `(N : k) ≠ 0` and "$N \cdot \Lambda = 0$" is `(N : Λ) = 0`; for parts 2 and 3 the hypotheses are `l.Prime`, `(l : k) ≠ 0` and `((l ^ m : ℕ) : Λ) = 0`. Vanishing is stated as `Subsingleton` of the Ext group in parts 1 and 2 (degrees $1$ and $n + 2$) and as `e = 0` for every `e` in degree $n + 3$ in part 3. $k$ and $\Lambda$ live in `Type`. The statement is not vacuous: for example $k$ the algebraic closure of $\mathbb{Q}$ and $\Lambda = \mathbb{Z}/\ell$ with $N = \ell$, $m = 1$.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V (the cohomology of curves); P. Deligne, SGA 4½, Cohomologie étale (Arcata), cohomology of curves

import Mathlib

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.etale_cohomology_affineLine_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] (Λ : Type) [CommRing Λ] :
    (∀ N : ℕ, (N : k) ≠ 0 → (N : Λ) = 0 →
      Subsingleton (CategoryTheory.Abelian.Ext
        ((CategoryTheory.constantSheaf (Spec (CommRingCat.of (Polynomial k))).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ))
        ((CategoryTheory.constantSheaf (Spec (CommRingCat.of (Polynomial k))).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) 1 : Type)) ∧
    (∀ l m : ℕ, l.Prime → (l : k) ≠ 0 → ((l ^ m : ℕ) : Λ) = 0 → ∀ n : ℕ,
      Subsingleton (CategoryTheory.Abelian.Ext
        ((CategoryTheory.constantSheaf (Spec (CommRingCat.of (Polynomial k))).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ))
        ((CategoryTheory.constantSheaf (Spec (CommRingCat.of (Polynomial k))).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) (n + 2) : Type)) ∧
    (∀ l m : ℕ, l.Prime → (l : k) ≠ 0 → ((l ^ m : ℕ) : Λ) = 0 →
      ∀ (F : CategoryTheory.Sheaf (Spec (CommRingCat.of (Polynomial k))).smallEtaleTopology (ModuleCat.{0} Λ)) (n : ℕ)
        (e : (CategoryTheory.Abelian.Ext
          ((CategoryTheory.constantSheaf (Spec (CommRingCat.of (Polynomial k))).smallEtaleTopology
          (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) F (n + 3) : Type)), e = 0) := by
  sorry
