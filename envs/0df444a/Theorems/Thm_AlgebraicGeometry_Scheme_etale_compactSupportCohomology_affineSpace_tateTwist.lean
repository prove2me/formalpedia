-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_etale_compactSupportCohomology_affineSpace_tateTwist
-- name    : AlgebraicGeometry.Scheme.etale_compactSupportCohomology_affineSpace_tateTwist
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-27T03:56:28.099385+00:00
-- url     : https://prove2.me/theorems/08afa25e-f00b-4c19-89a2-5fdc51980ec0
-- title:
--   Compactly supported étale cohomology of affine space with Tate twists: $H^{2n+2}_c(\mathbb{A}^{n+1}_K, \Lambda(n+1)) \cong \Lambda$, and $H^q_c(\mathbb{A}^{n+1}_K, \Lambda(k)) = 0$ for $q \ne 2n+2$
-- statement:
--   Let $K$ be an algebraically closed field, let $\ell$ be a prime different from the characteristic of $K$, and let $\Lambda$ be a finite commutative ring with $\ell^m \cdot \Lambda = 0$ for some $m \ge 0$. Let $\mu_{\ell^m} \subseteq K^\times$ be the group of $\ell^m$-th roots of unity and $T = \Lambda \otimes_{\mathbb{Z}} \mu_{\ell^m}$ (a free $\Lambda$-module of rank one). For $k \in \mathbb{Z}$ the Tate twist $\Lambda(k)$ is the constant étale sheaf with value $T^{\otimes k}$ if $k \ge 0$ and $(T^{\otimes(-k)})^\vee = \operatorname{Hom}_\Lambda(T^{\otimes(-k)}, \Lambda)$ if $k < 0$.
--
--   Affine space and its compactification in $(\mathbb{P}^1_K)^{n+1}$ are built as iterated fibre products over $K$. Let $\mathbb{A}^1_K = \operatorname{Spec} K[t]$, let $\mathbb{P}^1_K = \operatorname{Proj} K[X_0, X_1]$, and let $c\colon \mathbb{A}^1_K \to \mathbb{P}^1_K$, $t \mapsto [1 : t]$, be the standard chart, an open immersion onto $D_+(X_0)$. Put $X_0 = Z_0 = P_0 = \operatorname{Spec} K$ and $X_{k+1} = \mathbb{A}^1_K \times_K X_k$, $Z_{k+1} = \mathbb{P}^1_K \times_K Z_k$, $P_{k+1} = \mathbb{P}^1_K \times_K P_k$, with the open immersions $j_{k+1} = c \times j_k\colon X_{k+1} \to Z_{k+1}$ and the closed immersions (in fact isomorphisms) $i_{k+1} = \mathrm{id} \times i_k\colon Z_{k+1} \to P_{k+1}$, starting from $j_0 = i_0 = \mathrm{id}$. Then $X = X_{n+1} = \mathbb{A}^{n+1}_K$, $P = P_{n+1} \cong (\mathbb{P}^1_K)^{n+1}$ is proper over $K$, and $j = j_{n+1}$, $i = i_{n+1}$ present $\mathbb{A}^{n+1}_K$ as an open subscheme of $Z = Z_{n+1} \cong P$. For an étale sheaf $F$ of $\Lambda$-modules on $\mathbb{A}^{n+1}_K$ the cohomology with compact supports is
--
--   $$H^q_c(\mathbb{A}^{n+1}_K, F) = H^q(P, i_* j_! F) = \operatorname{Ext}^q(\underline{\Lambda}_P, i_* j_! F),$$
--
--   where $j_!$ is extension by zero and Ext is taken in the abelian category of étale sheaves of $\Lambda$-modules on $P$ (it is a $\Lambda$-module). Then:
--
--   1. $H^q_c(\mathbb{A}^{n+1}_K, \Lambda(k)) = 0$ for every twist $k \in \mathbb{Z}$ and every $q \ne 2n+2$;
--   2. $H^{2n+2}_c(\mathbb{A}^{n+1}_K, \Lambda(n+1)) \cong \Lambda$ as $\Lambda$-modules.
--
--   So the compactly supported cohomology of $\mathbb{A}^d_K$ ($d = n + 1 \ge 1$) is concentrated in the top degree $2d$, where it is free of rank one; with the twist $\Lambda(d)$ this is the trace isomorphism $H^{2d}_c(\mathbb{A}^d_K, \Lambda(d)) \cong \Lambda$ on which Poincaré duality is built (SGA 4, Exp. XVIII, 2.9; Milne, Étale Cohomology, VI.11). For $d = 1$ and untwisted coefficients this is the computation of $H^*_c(\mathbb{A}^1_K, \Lambda)$; here it holds in every dimension, for every Tate twist, and the top-degree isomorphism is $\Lambda$-linear.
--
--   **Formalization Note**: $\mathbb{P}^1_K$ is `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)` (grading `MvPolynomial.gradedAlgebra`, a local instance in the preamble) with structure map `π` pinned by `hπ` to `Proj.toSpecZero _ ≫ Spec.map (algebraMap K _)`; $\mathbb{A}^1_K$ is `Spec (.of (Polynomial K))` with structure map `ρ` pinned by `hρ` to `Spec.map Polynomial.C`. The chart is `c`, pinned by `hc` to `Spec.map φ ≫ Proj.awayι _ (X 0) _ one_pos`, where `φ` from the degree-zero part of $K[X_0,X_1]_{X_0}$ to $K[t]$ is pinned by `hφ`: it sends $a / X_0^d$ (`HomogeneousLocalization.Away.mk`) to $a(1, t)$ (`MvPolynomial.aeval ![1, Polynomial.X] a`); these fractions exhaust the ring, so `φ` is unique (and is an isomorphism). The tower is `D : ℕ → Σ X Z P, (X ⟶ Spec K) × (X ⟶ Z) × (Z ⟶ P) × (P ⟶ Spec K)` with `D k = ⟨X_k, Z_k, P_k, f_k, j_k, i_k, fbar_k⟩` ($f_k$, $\bar f_k$ the structure maps), pinned by `hD0` (everything `Spec K` and identities) and `hDs`: `X_(k+1) = pullback ρ f_k`, `Z_(k+1) = pullback (𝟙 _ ≫ π) (i_k ≫ fbar_k)`, `P_(k+1) = pullback π fbar_k`, `f_(k+1) = pullback.snd ≫ f_k`, `fbar_(k+1) = pullback.snd ≫ fbar_k`, and `j_(k+1)`, `i_(k+1)` the `pullback.map`s induced by $(c, j_k)$ and $(\mathrm{id}, i_k)$. `hDs` takes as premises the two commutativity facts `c ≫ π = ρ` and `j_k ≫ i_k ≫ fbar_k = f_k` that `pullback.map` needs; both hold (the second by induction), so `hD0` and `hDs` determine `D` uniquely. The scheme data in degree $n + 1$ are named by `hn : D (n + 1) = ⟨X, Z, P, f, j, i, fb⟩`. The twists are `tw : ℤ → ModuleCat Λ`, pinned by `htw` (`TensorPower Λ k (TensorProduct ℤ Λ (Additive (rootsOfUnity (l ^ m) K)))`) and `htw'` (its `Module.Dual` for `Int.negSucc k`, i.e. $k \mapsto -(k+1)$), and $\Lambda(k)$ is `(constantSheaf X.smallEtaleTopology (ModuleCat Λ)).obj (tw k)`. Étale sheaves are `CategoryTheory.Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ)`. The functors of small étale sites are pinned by equations: `Ei` to `MorphismProperty.Over.pullback` along $i$ and `Ej` to `MorphismProperty.Over.map` (composition with the étale $j$); $i_*$ is `sheafPushforwardContinuous` of `Ei` and $j_!$ is `sheafPullback` of `Ej` (the left adjoint of restriction, i.e. extension by zero). $H^q(P, -)$ is `Abelian.Ext` from the constant sheaf $\underline{\Lambda}_P$ = `(constantSheaf _ _).obj (ModuleCat.of Λ Λ)`, with Mathlib's $\Lambda$-module structure on `Ext`. The instance arguments (open immersion $j$, continuity of `Ei` and `Ej` for the étale topologies, existence of the left adjoint $j_!$) supply facts that Mathlib does not yet register as instances; they are Prop-valued and true, so they do not weaken the statement. Finiteness of $\Lambda$ is the explicit hypothesis `hΛfin`. The option `backward.isDefEq.respectTransparency.types false` lets Mathlib find `MorphismProperty.HasPullbacksAlong @Etale` for `Over.pullback`. The statement is not vacuous: the tower defined by the two recursion equations, the ring map $a / X_0^d \mapsto a(1, t)$ and the twists defined by `htw`, `htw'` satisfy every hypothesis, for every $n$.
-- source:
--   A. Grothendieck, M. Artin, J.-L. Verdier, SGA 4, Exposé XVIII, 2.9 (trace morphism, Tate twists) and Exposé XVII; P. Deligne, SGA 4 1/2, [Arcata] and [Dualité]; J. S. Milne, Étale Cohomology, Chapter VI §1 and §11

import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory Limits

theorem AlgebraicGeometry.Scheme.etale_compactSupportCohomology_affineSpace_tateTwist
    (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] (hΛfin : Finite Λ)
    (l : ℕ) (hl : l.Prime) (hlK : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (.of K))
    (hπ : π = Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0))))
    (ρ : Spec (.of (Polynomial K)) ⟶ Spec (.of K))
    (hρ : ρ = Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)))
    (φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) K)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) →+* Polynomial K)
    (hφ : ∀ (d : ℕ) (a : MvPolynomial (Fin 2) K)
      (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) K (d • 1)),
      φ (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin 2) K)
        (MvPolynomial.isHomogeneous_X K 0) d a ha) = MvPolynomial.aeval ![1, Polynomial.X] a)
    (c : Spec (.of (Polynomial K)) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))
    (hc : c = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 0)
        (MvPolynomial.isHomogeneous_X K 0) one_pos)
    (D : ℕ → Σ X : Scheme.{0}, Σ Z : Scheme.{0}, Σ P : Scheme.{0},
      (X ⟶ Spec (.of K)) × (X ⟶ Z) × (Z ⟶ P) × (P ⟶ Spec (.of K)))
    (hD0 : D 0 = ⟨Spec (.of K), Spec (.of K), Spec (.of K), 𝟙 _, 𝟙 _, 𝟙 _, 𝟙 _⟩)
    (hDs : ∀ (k : ℕ) (h0 : c ≫ π = ρ)
      (hk : (D k).2.2.2.2.1 ≫ (D k).2.2.2.2.2.1 ≫ (D k).2.2.2.2.2.2 = (D k).2.2.2.1),
      D (k + 1) = ⟨pullback ρ (D k).2.2.2.1,
        pullback (𝟙 _ ≫ π) ((D k).2.2.2.2.2.1 ≫ (D k).2.2.2.2.2.2),
        pullback π (D k).2.2.2.2.2.2,
        pullback.snd ρ (D k).2.2.2.1 ≫ (D k).2.2.2.1,
        pullback.map ρ (D k).2.2.2.1 (𝟙 _ ≫ π) ((D k).2.2.2.2.2.1 ≫ (D k).2.2.2.2.2.2)
          c (D k).2.2.2.2.1 (𝟙 _)
          ((Category.comp_id ρ).trans (h0.symm.trans (congrArg (c ≫ ·) (Category.id_comp π).symm)))
          ((Category.comp_id _).trans hk.symm),
        pullback.map (𝟙 _ ≫ π) ((D k).2.2.2.2.2.1 ≫ (D k).2.2.2.2.2.2) π (D k).2.2.2.2.2.2
          (𝟙 _) (D k).2.2.2.2.2.1 (𝟙 _) (Category.comp_id _) (Category.comp_id _),
        pullback.snd π (D k).2.2.2.2.2.2 ≫ (D k).2.2.2.2.2.2⟩)
    (tw : ℤ → ModuleCat.{0} Λ)
    (htw : ∀ k : ℕ, tw k = ModuleCat.of Λ
      (TensorPower Λ k (TensorProduct ℤ Λ (Additive (rootsOfUnity (l ^ m) K)))))
    (htw' : ∀ k : ℕ, tw (Int.negSucc k) = ModuleCat.of Λ
      (Module.Dual Λ (TensorPower Λ (k + 1) (TensorProduct ℤ Λ (Additive (rootsOfUnity (l ^ m) K))))))
    (n : ℕ) {X Z P : Scheme.{0}} (f : X ⟶ Spec (.of K)) (j : X ⟶ Z) [IsOpenImmersion j]
    (i : Z ⟶ P) (fb : P ⟶ Spec (.of K)) (hn : D (n + 1) = ⟨X, Z, P, f, j, i, fb⟩)
    (Ei : P.Etale ⥤ Z.Etale)
    (hEi : Ei = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) i)
    [Ei.IsContinuous P.smallEtaleTopology Z.smallEtaleTopology]
    (Ej : X.Etale ⥤ Z.Etale)
    (hEj : Ej = MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale j))
    [Ej.IsContinuous X.smallEtaleTopology Z.smallEtaleTopology]
    [(Ej.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      Z.smallEtaleTopology).IsRightAdjoint] :
    (∀ (k : ℤ) (q : ℕ), q ≠ 2 * n + 2 →
      ∀ e : (Abelian.Ext ((constantSheaf P.smallEtaleTopology (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ))
        ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) P.smallEtaleTopology Z.smallEtaleTopology).obj
          ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{0} Λ)).obj (tw k)))) q : Type), e = 0) ∧
    Nonempty ((Abelian.Ext ((constantSheaf P.smallEtaleTopology (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ))
        ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) P.smallEtaleTopology Z.smallEtaleTopology).obj
          ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{0} Λ)).obj (tw (n + 1))))) (2 * n + 2) : Type) ≃ₗ[Λ] Λ) := by
  sorry
