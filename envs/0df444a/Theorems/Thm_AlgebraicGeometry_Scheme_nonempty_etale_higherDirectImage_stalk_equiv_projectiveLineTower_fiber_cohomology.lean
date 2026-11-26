-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_higherDirectImage_stalk_equiv_projectiveLineTower_fiber_cohomology
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_higherDirectImage_stalk_equiv_projectiveLineTower_fiber_cohomology
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:21:07.155652+00:00
-- url     : https://prove2.me/theorems/18d6218f-c7f1-490f-8551-67237b6ce2ed
-- title:
--   Proper base change for iterated projective-line bundles: $(R^q f_* F)_s \cong H^q(X_s, F|_{X_s})$ for $X = (\mathbb{P}^1)^{n+1}_S \to S$ over an algebraically closed field
-- statement:
--   Let $K$ be an algebraically closed field, let $\ell$ be a prime different from the characteristic of $K$, and let $\Lambda$ be a finite commutative ring with $\ell^m \cdot \Lambda = 0$ for some $m \ge 0$. Let $S$ be a noetherian scheme locally of finite type over $K$ and let $s\colon \operatorname{Spec} K \to S$ be a $K$-rational point. Define the tower of iterated relative projective lines over $S$ by $X_0 = \mathbb{P}^1_S = \mathbb{P}^1_K \times_K S$ with $f_0\colon X_0 \to S$ the projection, and $X_{k+1} = \mathbb{P}^1_{X_k} = \mathbb{P}^1_K \times_K X_k$ with $f_{k+1}$ the composite $X_{k+1} \to X_k \to S$ of the projection and $f_k$; so $X_n \cong (\mathbb{P}^1_K)^{n+1} \times_K S$ and $f_n$ is proper. Let $X_{n,s} = X_n \times_S \operatorname{Spec} K$ be the fibre of $f_n$ over $s$, with inclusion $\iota\colon X_{n,s} \to X_n$. Then for every $n \ge 0$, every étale sheaf $F$ of $\Lambda$-modules on $X_n$ and every $q \ge 0$ there is an isomorphism of abelian groups
--
--   $$(R^q f_{n*} F)_s \;\cong\; H^q_{\mathrm{et}}(X_{n,s}, \iota^{*} F),$$
--
--   where $(R^q f_{n*} F)_s$ is the stalk at the geometric point $s$ of the $q$-th right derived functor of the direct image $f_{n*}$ on étale sheaves of $\Lambda$-modules, $\iota^{*}$ is the inverse image, and $H^q_{\mathrm{et}}(X_{n,s}, G) = \operatorname{Ext}^q(\underline{\Lambda}, G)$ is étale cohomology. This is the proper base change theorem (SGA 4, Exp. XII, XIII) for the proper morphisms $(\mathbb{P}^1)^{n+1}_S \to S$ at rational points, with torsion coefficients prime to the characteristic. In SGA 4 the general theorem is reduced, by Chow's lemma and dévissage, to composites of relative curves such as these towers of relative projective lines; the case $n = 0$ is the relative projective line itself.
--
--   **Formalization Note**: $\mathbb{P}^1_K$ is `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)` (grading `MvPolynomial.gradedAlgebra`, a local instance in the preamble) with structure map `π` pinned by `hπ` to `Proj.toSpecZero _ ≫ Spec.map (algebraMap K _)`. The tower is `T : ℕ → Σ Y : Scheme, Y ⟶ S` with `T k = ⟨X_k, f_k⟩`, pinned by `hT0 : T 0 = ⟨pullback π g, pullback.snd π g⟩` and `hTs : T (k + 1) = ⟨pullback π ((T k).2 ≫ g), pullback.snd π ((T k).2 ≫ g) ≫ (T k).2⟩`, where `(T k).2 ≫ g` is the structure map $X_k \to \operatorname{Spec} K$; so `T` is uniquely determined. The fibre is `pullback (T n).2 s` and $\iota$ its `pullback.fst`; `hs : s ≫ g = 𝟙 _` says that $s$ is a $K$-point. Étale sheaves are `CategoryTheory.Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ)`. The base-change functors of small étale sites are `E` and `E'`, pinned by `hE` and `hE'` to `MorphismProperty.Over.pullback` along $f_n$ and $\iota$; $f_{n*}$ is `E.sheafPushforwardContinuous`, $R^q f_{n*}$ is its `Functor.rightDerived q` (Mathlib's injective resolutions), $\iota^{*}$ is `E'.sheafPullback`, and the stalk is the fibre functor of `Scheme.pointSmallEtale s`. Four instance arguments supply facts that Mathlib does not yet register as instances (continuity of `E` and `E'` for the étale topologies, additivity of $f_{n*}$, existence of the inverse image along $\iota$); they are Prop-valued and true, so they do not weaken the statement. $H^q$ is `CategoryTheory.Abelian.Ext` with values in `Type`. Finiteness of $\Lambda$ is the explicit hypothesis `hΛfin`. The option `backward.isDefEq.respectTransparency.types false` lets Mathlib find `MorphismProperty.HasPullbacksAlong @Etale` for the base-change functors. The statement is not vacuous: $S = \operatorname{Spec} K$ with $g = s = \mathrm{id}$ and the tower defined by the two recursion equations satisfies every hypothesis, for every $n$.
-- source:
--   A. Grothendieck, M. Artin, J.-L. Verdier, SGA 4, Exposé XII (théorème de changement de base pour un morphisme propre, réduction au cas des courbes) and Exposé XIII; J. S. Milne, Étale Cohomology, Chapter VI §2

import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory Limits

theorem AlgebraicGeometry.Scheme.nonempty_etale_higherDirectImage_stalk_equiv_projectiveLineTower_fiber_cohomology
    (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] (hΛfin : Finite Λ)
    (l : ℕ) (hl : l.Prime) (hlK : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (S : Scheme.{0}) [IsNoetherian S] (g : S ⟶ Spec (.of K)) [LocallyOfFiniteType g]
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (.of K))
    (hπ : π = Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0))))
    (T : ℕ → Σ Y : Scheme.{0}, Y ⟶ S)
    (hT0 : T 0 = ⟨pullback π g, pullback.snd π g⟩)
    (hTs : ∀ k, T (k + 1) =
      ⟨pullback π ((T k).2 ≫ g), pullback.snd π ((T k).2 ≫ g) ≫ (T k).2⟩)
    (n : ℕ) (s : Spec (.of K) ⟶ S) (hs : s ≫ g = 𝟙 _)
    (E : S.Etale ⥤ (T n).1.Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (T n).2)
    [E.IsContinuous S.smallEtaleTopology (T n).1.smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      (T n).1.smallEtaleTopology).Additive]
    (E' : (T n).1.Etale ⥤ (pullback (T n).2 s).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.fst (T n).2 s))
    [E'.IsContinuous (T n).1.smallEtaleTopology (pullback (T n).2 s).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
      (pullback (T n).2 s).smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf (T n).1.smallEtaleTopology (ModuleCat.{0} Λ)) (q : ℕ) :
    Nonempty (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
        (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (T n).1.smallEtaleTopology).rightDerived q).obj F) ≃+
      (Abelian.Ext
        ((constantSheaf (pullback (T n).2 s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
          (ModuleCat.of Λ Λ))
        ((E'.sheafPullback (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
          (pullback (T n).2 s).smallEtaleTopology).obj F) q : Type)) := by
  sorry
