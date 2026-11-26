-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_natural_etale_compactSupport_stalk_equiv_projectiveLineTower_fiber_cohomology
-- name    : AlgebraicGeometry.Scheme.exists_natural_etale_compactSupport_stalk_equiv_projectiveLineTower_fiber_cohomology
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:14:21.476204+00:00
-- url     : https://prove2.me/theorems/80500da0-ddea-4ced-909d-6c0ccddfd1c8
-- title:
--   Proper base change with compact supports, natural in the sheaf: $(R^q f_! F)_s \cong H^q_c(X_s, F|_{X_s})$ for locally closed $X \subseteq (\mathbb{P}^1)^{n+1}_S$
-- statement:
--   Let $K$ be an algebraically closed field, let $\ell$ be a prime different from the characteristic of $K$, and let $\Lambda$ be a finite commutative ring with $\ell^m \cdot \Lambda = 0$ for some $m \ge 0$. Let $S$ be a noetherian scheme locally of finite type over $K$ and let $s\colon \operatorname{Spec} K \to S$ be a $K$-rational point. Let $\bar f\colon P = P_n \to S$ be the iterated relative projective line: $P_0 = \mathbb{P}^1_K \times_K S$ and $P_{k+1} = \mathbb{P}^1_K \times_K P_k$, so $P_n \cong (\mathbb{P}^1_K)^{n+1} \times_K S$ and $\bar f$ is proper. Let $X$ be a locally closed subscheme of $P$, presented as an open immersion $j\colon X \to Z$ followed by a closed immersion $i\colon Z \to P$, and let $f = \bar f \circ i \circ j\colon X \to S$. For étale sheaves $F$ of $\Lambda$-modules on $X$ put $R^q f_! F = R^q \bar f_* (i_* j_! F)$, where $j_!$ is extension by zero (the left adjoint of restriction $j^*$). Let $P_s = P \times_S \operatorname{Spec} K$, $Z_s = Z \times_P P_s$ and $X_s = X \times_Z Z_s$ be the geometric fibres, with $j_s\colon X_s \to Z_s$, $i_s\colon Z_s \to P_s$ the base-changed immersions and $\iota\colon X_s \to X$ the inclusion, and put $H^q_c(X_s, G) = H^q_{\mathrm{et}}(P_s, i_{s*} j_{s!} G)$ with $H^q_{\mathrm{et}}(P_s, -) = \operatorname{Ext}^q(\underline{\Lambda}, -)$. Then for every $q \ge 0$ there are isomorphisms of abelian groups
--
--   $$e_F\colon (R^q f_! F)_s \;\xrightarrow{\ \sim\ }\; H^q_c(X_s, \iota^{*} F),$$
--
--   one for every étale sheaf $F$ of $\Lambda$-modules on $X$, which are natural in $F$: for every morphism $\varphi\colon F \to F'$ the square formed by $e_F$, $e_{F'}$, the map of stalks $(R^q f_! \varphi)_s$ and the map $H^q_c(X_s, \iota^{*}\varphi)$ (composition with the class of $i_{s*} j_{s!} \iota^{*} \varphi$ in $\operatorname{Ext}^0$) commutes. This is the proper base change theorem for cohomology with compact supports (SGA 4, Exp. XVII, 5.2.8; Milne, Étale Cohomology, VI.3) for all schemes that embed as locally closed subschemes of $(\mathbb{P}^1)^{n+1}_S$, which include every affine scheme of finite type over an affine $S$ (a closed subscheme of $\mathbb{A}^{n+1}_S \subseteq (\mathbb{P}^1)^{n+1}_S$), in the canonical form: the identification of the stalks of $R^q f_!$ with compactly supported cohomology of the geometric fibre is a natural isomorphism of functors of $F$, not just an abstract isomorphism for each $F$.
--
--   **Formalization Note**: $\mathbb{P}^1_K$ is `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)` (grading `MvPolynomial.gradedAlgebra`, a local instance in the preamble) with structure map `π` pinned by `hπ` to `Proj.toSpecZero _ ≫ Spec.map (algebraMap K _)`. The tower is `T : ℕ → Σ Y : Scheme, Y ⟶ S` with `T k = ⟨P_k, f_k⟩`, pinned by `hT0 : T 0 = ⟨pullback π g, pullback.snd π g⟩` and `hTs : T (k + 1) = ⟨pullback π ((T k).2 ≫ g), pullback.snd π ((T k).2 ≫ g) ≫ (T k).2⟩`, so `T` is uniquely determined and $\bar f$ = `(T n).2`. `hs : s ≫ g = 𝟙 _` says that $s$ is a $K$-point. The fibres are $P_s$ = `pullback (T n).2 s`, $Z_s$ = `pullback i (pullback.fst (T n).2 s)` and $X_s$ = `pullback j (pullback.fst i (pullback.fst (T n).2 s))`, with $i_s$, $j_s$ the `pullback.snd` maps and $\iota$ = `pullback.fst j _`. Étale sheaves are `CategoryTheory.Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ)`. The functors of small étale sites are pinned by equations: `E`, `Ei`, `Eis`, `EX` to `MorphismProperty.Over.pullback` along $\bar f$, $i$, $i_s$ and $\iota$, and `Ej`, `Ejs` to `MorphismProperty.Over.map` (composition with the étale maps $j$, $j_s$). Then $\bar f_*$, $i_*$, $i_{s*}$ are `sheafPushforwardContinuous` of `E`, `Ei`, `Eis`; $R^q \bar f_*$ is `Functor.rightDerived q` (Mathlib's injective resolutions); $j_!$, $j_{s!}$ are `sheafPullback` of `Ej`, `Ejs` (the left adjoints of the restrictions `Ej.sheafPushforwardContinuous`, `Ejs.sheafPushforwardContinuous`, i.e. extension by zero); $\iota^{*}$ is `EX.sheafPullback`; the stalk is the fibre functor of `Scheme.pointSmallEtale s`. The instance arguments (continuity of the six functors for the étale topologies, additivity of $\bar f_*$, existence of the three left adjoints) supply facts that Mathlib does not yet register as instances; they are Prop-valued and true, so they do not weaken the statement. $H^q$ is `CategoryTheory.Abelian.Ext` with values in `Type`, and $H^q_c(X_s, \iota^*\varphi)$ is `Ext.comp` with `Ext.mk₀`. Finiteness of $\Lambda$ is the explicit hypothesis `hΛfin`. The option `backward.isDefEq.respectTransparency.types false` lets Mathlib find `MorphismProperty.HasPullbacksAlong @Etale` for the base-change functors. The statement is not vacuous: $S = \operatorname{Spec} K$, $g = s = \mathrm{id}$, the tower defined by the two recursion equations and $X = Z = P$ with $j = i = \mathrm{id}$ satisfy every hypothesis, for every $n$ and $q$.
-- source:
--   A. Grothendieck, M. Artin, J.-L. Verdier, SGA 4, Exposé XII (changement de base propre) and Exposé XVII, 5.2.8 (changement de base pour R f_!); J. S. Milne, Étale Cohomology, Chapter VI §2-§3

import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory Limits

theorem AlgebraicGeometry.Scheme.exists_natural_etale_compactSupport_stalk_equiv_projectiveLineTower_fiber_cohomology
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
    {X Z : Scheme.{0}} (j : X ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ (T n).1) [IsClosedImmersion i]
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
    (Eis : (pullback (T n).2 s).Etale ⥤ (pullback i (pullback.fst (T n).2 s)).Etale)
    (hEis : Eis = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.snd i (pullback.fst (T n).2 s)))
    [Eis.IsContinuous (pullback (T n).2 s).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology]
    (Ejs : (pullback j (pullback.fst i (pullback.fst (T n).2 s))).Etale ⥤
      (pullback i (pullback.fst (T n).2 s)).Etale)
    (hEjs : Ejs = MorphismProperty.Over.map (P := @Etale) ⊤
      (inferInstance : Etale (pullback.snd j (pullback.fst i (pullback.fst (T n).2 s)))))
    [Ejs.IsContinuous (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology]
    [(Ejs.sheafPushforwardContinuous (ModuleCat.{0} Λ)
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).IsRightAdjoint]
    (EX : X.Etale ⥤ (pullback j (pullback.fst i (pullback.fst (T n).2 s))).Etale)
    (hEX : EX = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.fst j (pullback.fst i (pullback.fst (T n).2 s))))
    [EX.IsContinuous X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology]
    [(EX.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).IsRightAdjoint]
    (q : ℕ) :
    ∃ e : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ),
        (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).obj
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).obj
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).obj F))) ≃+
        (Abelian.Ext
          ((constantSheaf (pullback (T n).2 s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
            (ModuleCat.of Λ Λ))
          ((Eis.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 s).smallEtaleTopology
            (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).obj
            ((Ejs.sheafPullback (ModuleCat.{0} Λ)
              (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
              (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).obj
              ((EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
                (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).obj F))) q :
          Type)),
      ∀ (F F' : Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ)) (φ : F ⟶ F')
        (y : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).obj
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).obj
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).obj F)))),
        e F' ((((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).map
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).map
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).map
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).map φ)))).hom y) =
        (e F y).comp (Abelian.Ext.mk₀
          ((Eis.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 s).smallEtaleTopology
            (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).map
            ((Ejs.sheafPullback (ModuleCat.{0} Λ)
              (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
              (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).map
              ((EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
                (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).map φ))))
          (add_zero q) := by
  sorry
