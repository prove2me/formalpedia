-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_compactSupport_baseChange_natIso_projectiveLineTower
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_compactSupport_baseChange_natIso_projectiveLineTower
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-27T00:42:05.810616+00:00
-- url     : https://prove2.me/theorems/568b624a-d21e-5be6-b7e4-8ea27e1ae0b2
-- title:
--   Sheaf-level proper base change with compact supports: $g^* R^q f_! \cong R^q f'_! \, g_X^*$ for locally closed $X \subseteq (\mathbb{P}^1)^{n+1}_S$ and any $g\colon S' \to S$ of finite type
-- statement:
--   Let $K$ be an algebraically closed field, let $\ell$ be a prime different from the characteristic of $K$, and let $\Lambda$ be a finite commutative ring with $\ell^m \cdot \Lambda = 0$ for some $m \ge 0$. Let $S$ be a noetherian scheme locally of finite type over $K$, and let $g\colon S' \to S$ be a morphism from a noetherian scheme $S'$ that is locally of finite type over $K$ (via $S' \to S \to \operatorname{Spec} K$). Let $\bar f\colon P = P_n \to S$ be the iterated relative projective line: $P_0 = \mathbb{P}^1_K \times_K S$ and $P_{k+1} = \mathbb{P}^1_K \times_K P_k$, so $P_n \cong (\mathbb{P}^1_K)^{n+1} \times_K S$ and $\bar f$ is proper. Let $X$ be a locally closed subscheme of $P$, presented as an open immersion $j\colon X \to Z$ followed by a closed immersion $i\colon Z \to P$, and let $f = \bar f \circ i \circ j\colon X \to S$. For étale sheaves $F$ of $\Lambda$-modules on $X$ put $R^q f_! F = R^q \bar f_* (i_* j_! F)$, where $j_!$ is extension by zero (the left adjoint of restriction $j^*$). Base change along $g$: $P' = P \times_S S'$ with projection $\bar f'\colon P' \to S'$, $Z' = Z \times_P P'$, $X' = X \times_Z Z'$, with $j'\colon X' \to Z'$, $i'\colon Z' \to P'$ the base-changed immersions and $g_X\colon X' \to X$ the projection, and $R^q f'_! G = R^q \bar f'_* (i'_* j'_! G)$ for $f' = \bar f' \circ i' \circ j'\colon X' \to S'$. Then for every $q \ge 0$ there is an isomorphism of functors from étale sheaves of $\Lambda$-modules on $X$ to étale sheaves of $\Lambda$-modules on $S'$
--
--   $$g^{*} \circ R^q f_! \;\cong\; R^q f'_! \circ g_X^{*},$$
--
--   that is, isomorphisms $g^{*} R^q f_! F \cong R^q f'_! (g_X^{*} F)$ natural in $F$. This is the proper base change theorem for cohomology with compact supports at the level of sheaves (SGA 4, Exp. XVII, 5.2.8; Milne, Étale Cohomology, VI.3), for every scheme that embeds as a locally closed subscheme of $(\mathbb{P}^1)^{n+1}_S$ (for example every affine scheme of finite type over an affine $S$, a closed subscheme of $\mathbb{A}^{n+1}_S \subseteq (\mathbb{P}^1)^{n+1}_S$) and every base change $g$ of finite type, not only geometric points.
--
--   **Formalization Note**: $\mathbb{P}^1_K$ is `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)` (grading `MvPolynomial.gradedAlgebra`, a local instance in the preamble) with structure map `π` pinned by `hπ` to `Proj.toSpecZero _ ≫ Spec.map (algebraMap K _)`. The structure map of $S$ is `gS : S ⟶ Spec K`. The tower is `T : ℕ → Σ Y : Scheme, Y ⟶ S` with `T k = ⟨P_k, f_k⟩`, pinned by `hT0 : T 0 = ⟨pullback π gS, pullback.snd π gS⟩` and `hTs : T (k + 1) = ⟨pullback π ((T k).2 ≫ gS), pullback.snd π ((T k).2 ≫ gS) ≫ (T k).2⟩`, so `T` is uniquely determined and $\bar f$ = `(T n).2`. The base change is $P'$ = `pullback (T n).2 g` with $\bar f'$ = `pullback.snd (T n).2 g`, $Z'$ = `pullback i (pullback.fst (T n).2 g)` and $X'$ = `pullback j (pullback.fst i (pullback.fst (T n).2 g))`, with $i'$, $j'$ the `pullback.snd` maps and $g_X$ = `pullback.fst j _`. Étale sheaves are `CategoryTheory.Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ)`. The functors of small étale sites are pinned by equations: `E`, `Ei`, `Eg`, `E'`, `Ei'`, `EX` to `MorphismProperty.Over.pullback` along $\bar f$, $i$, $g$, $\bar f'$, $i'$ and $g_X$, and `Ej`, `Ej'` to `MorphismProperty.Over.map` (composition with the étale maps $j$, $j'$). Then $\bar f_*$, $i_*$, $\bar f'_*$, $i'_*$ are `sheafPushforwardContinuous` of `E`, `Ei`, `E'`, `Ei'`; $R^q \bar f_*$, $R^q \bar f'_*$ are `Functor.rightDerived q` (Mathlib's injective resolutions); $j_!$, $j'_!$ are `sheafPullback` of `Ej`, `Ej'` (the left adjoints of the restrictions, i.e. extension by zero); $g^*$ and $g_X^*$ are `sheafPullback` of `Eg` and `EX`. The conclusion is `Nonempty` of an isomorphism between the two composite functors (`⋙`), i.e. a natural isomorphism. The instance arguments (continuity of the eight functors for the étale topologies, additivity of $\bar f_*$ and $\bar f'_*$, existence of the four left adjoints) supply facts that Mathlib does not yet register as instances; they are Prop-valued and true, so they do not weaken the statement. Finiteness of $\Lambda$ is the explicit hypothesis `hΛfin`. The option `backward.isDefEq.respectTransparency.types false` lets Mathlib find `MorphismProperty.HasPullbacksAlong @Etale` for the base-change functors. The statement is not vacuous: $S = S' = \operatorname{Spec} K$, $gS = g = \mathrm{id}$, the tower defined by the two recursion equations and $X = Z = P$ with $j = i = \mathrm{id}$ satisfy every hypothesis, for every $n$ and $q$.
-- source:
--   A. Grothendieck, M. Artin, J.-L. Verdier, SGA 4, Exposé XII (changement de base propre) and Exposé XVII, 5.2.8 (changement de base pour R f_!); J. S. Milne, Étale Cohomology, Chapter VI §2-§3

import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory Limits

theorem AlgebraicGeometry.Scheme.nonempty_etale_compactSupport_baseChange_natIso_projectiveLineTower
    (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] (hΛfin : Finite Λ)
    (l : ℕ) (hl : l.Prime) (hlK : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (S : Scheme.{0}) [IsNoetherian S] (gS : S ⟶ Spec (.of K)) [LocallyOfFiniteType gS]
    (S' : Scheme.{0}) [IsNoetherian S'] (g : S' ⟶ S) [LocallyOfFiniteType (g ≫ gS)]
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (.of K))
    (hπ : π = Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0))))
    (T : ℕ → Σ Y : Scheme.{0}, Y ⟶ S)
    (hT0 : T 0 = ⟨pullback π gS, pullback.snd π gS⟩)
    (hTs : ∀ k, T (k + 1) =
      ⟨pullback π ((T k).2 ≫ gS), pullback.snd π ((T k).2 ≫ gS) ≫ (T k).2⟩)
    (n : ℕ) {X Z : Scheme.{0}} (j : X ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ (T n).1) [IsClosedImmersion i]
    (E : S.Etale ⥤ (T n).1.Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (T n).2)
    [E.IsContinuous S.smallEtaleTopology (T n).1.smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      (T n).1.smallEtaleTopology).Additive]
    (Ei : (T n).1.Etale ⥤ Z.Etale)
    (hEi : Ei = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) i)
    [Ei.IsContinuous (T n).1.smallEtaleTopology Z.smallEtaleTopology]
    (Ej : X.Etale ⥤ Z.Etale)
    (hEj : Ej = MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale j))
    [Ej.IsContinuous X.smallEtaleTopology Z.smallEtaleTopology]
    [(Ej.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      Z.smallEtaleTopology).IsRightAdjoint]
    (Eg : S.Etale ⥤ S'.Etale)
    (hEg : Eg = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) g)
    [Eg.IsContinuous S.smallEtaleTopology S'.smallEtaleTopology]
    [(Eg.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      S'.smallEtaleTopology).IsRightAdjoint]
    (E' : S'.Etale ⥤ (pullback (T n).2 g).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.snd (T n).2 g))
    [E'.IsContinuous S'.smallEtaleTopology (pullback (T n).2 g).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) S'.smallEtaleTopology
      (pullback (T n).2 g).smallEtaleTopology).Additive]
    (Ei' : (pullback (T n).2 g).Etale ⥤ (pullback i (pullback.fst (T n).2 g)).Etale)
    (hEi' : Ei' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.snd i (pullback.fst (T n).2 g)))
    [Ei'.IsContinuous (pullback (T n).2 g).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology]
    (Ej' : (pullback j (pullback.fst i (pullback.fst (T n).2 g))).Etale ⥤
      (pullback i (pullback.fst (T n).2 g)).Etale)
    (hEj' : Ej' = MorphismProperty.Over.map (P := @Etale) ⊤
      (inferInstance : Etale (pullback.snd j (pullback.fst i (pullback.fst (T n).2 g)))))
    [Ej'.IsContinuous (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology]
    [(Ej'.sheafPushforwardContinuous (ModuleCat.{0} Λ)
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology).IsRightAdjoint]
    (EX : X.Etale ⥤ (pullback j (pullback.fst i (pullback.fst (T n).2 g))).Etale)
    (hEX : EX = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.fst j (pullback.fst i (pullback.fst (T n).2 g))))
    [EX.IsContinuous X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology]
    [(EX.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology).IsRightAdjoint]
    (q : ℕ) :
    Nonempty
      (Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology ⋙
        Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology Z.smallEtaleTopology ⋙
        (E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (T n).1.smallEtaleTopology).rightDerived q ⋙
        Eg.sheafPullback (ModuleCat.{0} Λ) S.smallEtaleTopology S'.smallEtaleTopology ≅
      EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
          (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology ⋙
        Ej'.sheafPullback (ModuleCat.{0} Λ)
          (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
          (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology ⋙
        Ei'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 g).smallEtaleTopology
          (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology ⋙
        (E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) S'.smallEtaleTopology
          (pullback (T n).2 g).smallEtaleTopology).rightDerived q) := by
  sorry
