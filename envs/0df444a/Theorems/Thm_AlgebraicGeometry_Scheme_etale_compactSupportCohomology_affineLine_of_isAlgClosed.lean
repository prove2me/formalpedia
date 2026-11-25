-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_etale_compactSupportCohomology_affineLine_of_isAlgClosed
-- name    : AlgebraicGeometry.Scheme.etale_compactSupportCohomology_affineLine_of_isAlgClosed
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-25T11:56:51.711082+00:00
-- url     : https://prove2.me/theorems/7f91d51e-b39b-511d-a427-01a6ba1bc462
-- title:
--   Compactly supported étale cohomology of the affine line: $H^*_c(\mathbb{A}^1_k, \Lambda) = 0, 0, \Lambda, 0, 0, \dots$ for $k$ algebraically closed
-- statement:
--   Let $k$ be an algebraically closed field, let $\mathbb{P}^1_k = \operatorname{Proj} k[X_0, X_1]$ be the projective line over $k$, and let $j\colon \mathbb{A}^1_k = D_+(X_0) \hookrightarrow \mathbb{P}^1_k$ be the standard affine chart, the open subscheme where $X_0 \ne 0$; its complement is the point $\infty = [0:1]$. Let $\Lambda$ be a commutative ring and $\underline{\Lambda}$ the constant sheaf of $\Lambda$-modules on the small étale site of $\mathbb{P}^1_k$. Let $G$ be an étale sheaf of $\Lambda$-modules on $\mathbb{P}^1_k$ together with a morphism $\iota\colon G \to \underline{\Lambda}$ such that, for every geometric point $\bar x\colon \operatorname{Spec}\Omega \to \mathbb{P}^1_k$ ($\Omega$ a separably closed field), the stalk map $\iota_{\bar x}\colon G_{\bar x} \to \Lambda$ is an isomorphism if $\bar x$ lies in $\mathbb{A}^1_k$, and $G_{\bar x} = 0$ if $\bar x$ lies over $\infty$. These conditions say exactly that $G$ is the extension by zero $j_!\Lambda$ of the constant sheaf on $\mathbb{A}^1_k$ (such a pair $(G, \iota)$ exists and is unique up to unique isomorphism), so that
--
--   $$H^q_c(\mathbb{A}^1_k, \Lambda) = H^q(\mathbb{P}^1_k, j_!\Lambda) = \operatorname{Ext}^q(\underline{\Lambda}, G)$$
--
--   is the compactly supported étale cohomology of the affine line (Ext in the abelian category of étale sheaves of $\Lambda$-modules on $\mathbb{P}^1_k$). Then:
--
--   1. $H^0_c(\mathbb{A}^1_k, \Lambda) = 0$, for every $\Lambda$.
--   2. If $N$ is a natural number that is nonzero in $k$ and $N \cdot \Lambda = 0$, then $H^1_c(\mathbb{A}^1_k, \Lambda) = 0$.
--   3. If $\ell$ is a prime different from the characteristic of $k$, $n \ge 1$ and $\ell^n \cdot \Lambda = 0$, then $H^2_c(\mathbb{A}^1_k, \Lambda) \cong \Lambda$ as abelian groups.
--   4. If $\ell$ is a prime different from the characteristic of $k$ and $\ell^m \cdot \Lambda = 0$ for some $m \ge 0$, then $H^q_c(\mathbb{A}^1_k, \Lambda) = 0$ for every $q \ge 3$.
--
--   So for $\Lambda = \mathbb{Z}/\ell^n$ with $\ell \ne \operatorname{char} k$ the compactly supported cohomology of the affine line is $\Lambda$ in degree $2$ and $0$ in every other degree, the same answer as for the plane $\mathbb{R}^2$; by contrast the ordinary cohomology $H^*(\mathbb{A}^1_k, \Lambda)$ is $\Lambda$ in degree $0$ only. This is the basic example behind Poincaré duality for curves, $H^q_c(\mathbb{A}^1) \times H^{2-q}(\mathbb{A}^1) \to H^2_c(\mathbb{A}^1) \cong \Lambda$, and the first step of the computation of $R f_!$ for curves.
--
--   **Formalization Note**: $\mathbb{P}^1_k$ is `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)` (the grading `MvPolynomial.gradedAlgebra` is made a local instance in the preamble) and $\mathbb{A}^1_k$ is its basic open `Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0)`. Étale sheaves of $\Lambda$-modules are `Sheaf (Proj _).smallEtaleTopology (ModuleCat.{0} Λ)`, $\underline{\Lambda}$ is `(constantSheaf _ (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)`, and $H^q$ is `Abelian.Ext` with values in `Type`, for the `HasExt` structure that Mathlib provides on this Grothendieck abelian category. Mathlib has no extension-by-zero functor $j_!$ for étale sheaves, so $j_!\Lambda$ is given as the variable `G` with the map `ι : G ⟶ Λ` and the two stalk conditions `hU` and `hZ`. A geometric point is a morphism `p : Spec (CommRingCat.of Ω) ⟶ Proj _` with `Ω` a separably closed field in `Type`, it lies in $\mathbb{A}^1_k$ when `p default ∈ Proj.basicOpen _ (MvPolynomial.X 0)` (the image of the unique point of `Spec Ω`), and the stalk at it is `(Scheme.pointSmallEtale p).sheafFiber`, Mathlib's fibre functor of the corresponding point of the small étale site. `hU` asks that the stalk map of `ι` be an isomorphism at the geometric points of $\mathbb{A}^1_k$ and `hZ` that the stalk of `G` be zero at the geometric points over $\infty$; these hypotheses hold for $j_!\Lambda$ with its canonical inclusion into $\underline{\Lambda}$ and determine $(G, \iota)$ up to isomorphism, since the stalks at geometric points detect isomorphisms of étale sheaves. The parts are stated as `e = 0` for every `e` in degrees $0$, $1$ and $n + 3$, and as `Nonempty (Ext^2 ≃+ Λ)` (an isomorphism of additive groups) in degree $2$; the hypotheses of each part are those listed above. $k$ and $\Lambda$ live in `Type`. The statement is not vacuous: for example $k$ the algebraic closure of $\mathbb{Q}$ and $\Lambda = \mathbb{Z}/\ell$, where part 3 says $H^2_c(\mathbb{A}^1_k, \mathbb{Z}/\ell) \cong \mathbb{Z}/\ell \ne 0$.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.etale_compactSupportCohomology_affineLine_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] (Λ : Type) [CommRing Λ]
    (G : Sheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology (ModuleCat.{0} Λ))
    (ι : G ⟶ (constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
      (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ))
    (hU : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
      (p : Spec (CommRingCat.of Ω) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)),
      p default ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0) →
        IsIso ((Scheme.pointSmallEtale p).sheafFiber (A := ModuleCat.{0} Λ) |>.map ι))
    (hZ : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
      (p : Spec (CommRingCat.of Ω) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)),
      p default ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0) →
        Limits.IsZero ((Scheme.pointSmallEtale p).sheafFiber (A := ModuleCat.{0} Λ) |>.obj G)) :
    (∀ e : (Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
        (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G 0 : Type), e = 0) ∧
    (∀ N : ℕ, (N : k) ≠ 0 → (N : Λ) = 0 →
      ∀ e : (Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
        (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G 1 : Type), e = 0) ∧
    (∀ l n : ℕ, l.Prime → 0 < n → (l : k) ≠ 0 → ((l ^ n : ℕ) : Λ) = 0 →
      Nonempty ((Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
        (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G 2 : Type) ≃+ Λ)) ∧
    (∀ l m : ℕ, l.Prime → (l : k) ≠ 0 → ((l ^ m : ℕ) : Λ) = 0 →
      ∀ (n : ℕ) (e : (Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
        (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G (n + 3) : Type)), e = 0) := by
  sorry
