-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_higherDirectImage_stalk_equiv_projectiveLine_fiber_cohomology
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_higherDirectImage_stalk_equiv_projectiveLine_fiber_cohomology
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:02:22.183347+00:00
-- url     : https://prove2.me/theorems/deb7ba8e-ce9c-4977-ba08-3eb5e1ec16eb
-- title:
--   Proper base change for the projective line: $(R^q g_* F)_s \cong H^q(\mathbb{P}^1_s, F|_{\mathbb{P}^1_s})$ over a base of finite type over an algebraically closed field
-- statement:
--   Let $K$ be an algebraically closed field, let $\ell$ be a prime different from the characteristic of $K$, and let $\Lambda$ be a finite commutative ring with $\ell^m \cdot \Lambda = 0$ for some $m \ge 0$. Let $S$ be a noetherian scheme locally of finite type over $K$, let $g\colon \mathbb{P}^1_S = \mathbb{P}^1_K \times_K S \to S$ be the relative projective line, and let $s\colon \operatorname{Spec} K \to S$ be a $K$-rational point, with fibre $\mathbb{P}^1_s = \mathbb{P}^1_S \times_S \operatorname{Spec} K$ and inclusion $\iota\colon \mathbb{P}^1_s \to \mathbb{P}^1_S$. Then for every étale sheaf $F$ of $\Lambda$-modules on $\mathbb{P}^1_S$ and every $q \ge 0$ there is an isomorphism of abelian groups
--
--   $$(R^q g_* F)_s \;\cong\; H^q_{\mathrm{et}}(\mathbb{P}^1_s, \iota^{*} F),$$
--
--   where $(R^q g_* F)_s$ is the stalk at the geometric point $s$ of the $q$-th right derived functor of the direct image $g_*$ on étale sheaves of $\Lambda$-modules, $\iota^{*}$ is the inverse image, and $H^q_{\mathrm{et}}(\mathbb{P}^1_s, G) = \operatorname{Ext}^q(\underline{\Lambda}, G)$ is étale cohomology. This is the proper base change theorem (SGA 4, Exp. XII, XIII) for the proper morphism $\mathbb{P}^1_S \to S$ at rational points, with torsion coefficients prime to the characteristic. In SGA 4 the case of relative curves, and in particular of $\mathbb{P}^1$, is the key step: the general theorem is reduced to it by Chow's lemma and dévissage.
--
--   **Formalization Note**: $\mathbb{P}^1_K$ is `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)` (grading `MvPolynomial.gradedAlgebra`, a local instance in the preamble) with structure map `π` pinned by `hπ` to `Proj.toSpecZero _ ≫ Spec.map (algebraMap K _)`; $\mathbb{P}^1_S$ is `pullback π g`, $g$ is `pullback.snd π g`, the fibre is `pullback (pullback.snd π g) s` and $\iota$ its `pullback.fst`; `hs : s ≫ g = 𝟙 _` says that $s$ is a $K$-point. Étale sheaves are `CategoryTheory.Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ)`. The base-change functors of small étale sites are `E` and `E'`, pinned by `hE` and `hE'` to `MorphismProperty.Over.pullback` along $g$ and $\iota$; $g_*$ is `E.sheafPushforwardContinuous`, $R^q g_*$ is its `Functor.rightDerived q` (Mathlib's injective resolutions), $\iota^{*}$ is `E'.sheafPullback`, and the stalk is the fibre functor of `Scheme.pointSmallEtale s`. Four instance arguments supply facts that Mathlib does not yet register as instances (continuity of `E` and `E'` for the étale topologies, additivity of $g_*$, existence of the inverse image along $\iota$); they are Prop-valued and true, so they do not weaken the statement. $H^q$ is `CategoryTheory.Abelian.Ext` with values in `Type`. Finiteness of $\Lambda$ is the explicit hypothesis `hΛfin`. The option `backward.isDefEq.respectTransparency.types false` lets Mathlib find `MorphismProperty.HasPullbacksAlong @Etale` for the base-change functors. The statement is not vacuous: $S = \operatorname{Spec} K$ with $g = s = \mathrm{id}$ satisfies every hypothesis.
-- source:
--   A. Grothendieck, M. Artin, J.-L. Verdier, SGA 4, Exposé XII (théorème de changement de base pour un morphisme propre, réduction au cas des courbes) and Exposé XIII; J. S. Milne, Étale Cohomology, Chapter VI §2

import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory Limits

theorem AlgebraicGeometry.Scheme.nonempty_etale_higherDirectImage_stalk_equiv_projectiveLine_fiber_cohomology
    (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] (hΛfin : Finite Λ)
    (l : ℕ) (hl : l.Prime) (hlK : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (S : Scheme.{0}) [IsNoetherian S] (g : S ⟶ Spec (.of K)) [LocallyOfFiniteType g]
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (.of K))
    (hπ : π = Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0))))
    (s : Spec (.of K) ⟶ S) (hs : s ≫ g = 𝟙 _)
    (E : S.Etale ⥤ (pullback π g).Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.snd π g))
    [E.IsContinuous S.smallEtaleTopology (pullback π g).smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology (pullback π g).smallEtaleTopology).Additive]
    (E' : (pullback π g).Etale ⥤ (pullback (pullback.snd π g) s).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.fst (pullback.snd π g) s))
    [E'.IsContinuous (pullback π g).smallEtaleTopology (pullback (pullback.snd π g) s).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback π g).smallEtaleTopology
      (pullback (pullback.snd π g) s).smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf (pullback π g).smallEtaleTopology (ModuleCat.{0} Λ)) (q : ℕ) :
    Nonempty (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
        (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (pullback π g).smallEtaleTopology).rightDerived q).obj F) ≃+
      (Abelian.Ext
        ((constantSheaf (pullback (pullback.snd π g) s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
          (ModuleCat.of Λ Λ))
        ((E'.sheafPullback (ModuleCat.{0} Λ) (pullback π g).smallEtaleTopology
          (pullback (pullback.snd π g) s).smallEtaleTopology).obj F) q : Type)) := by
  sorry
