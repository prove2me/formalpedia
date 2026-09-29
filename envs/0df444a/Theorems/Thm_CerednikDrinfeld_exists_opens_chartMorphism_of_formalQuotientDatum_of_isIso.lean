-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_opens_chartMorphism_of_formalQuotientDatum_of_isIso
-- name    : CerednikDrinfeld.exists_opens_chartMorphism_of_formalQuotientDatum_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/1202def6-0a82-5de8-9500-2fcca02e9fc6
-- title:
--   Chart data transported from a formal quotient datum to X
-- statement:
--   Fix a natural number $r$, a commutative ring $\mathcal O$ with an element $\pi$, a field $K_0$ which is an $\mathcal O$-algebra, a commutative $\mathcal O$-algebra $O^{nr}$ equipped with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, a group homomorphism $v\det : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively), a group $G$ with a homomorphism $\sigma : G \to \mathrm{GL}_2(K_0)$ and two subgroups $\Gamma, \Gamma' \le G$, a scheme $\mathcal X$ and a morphism $f : \mathcal X \to \operatorname{Spec}\mathcal O$, an element $g_1 \in \mathrm{GL}_2(K_0)$, and a family $\Theta$ which assigns, to every $\mathcal O$-algebra $B$ in which the image of $\pi$ is nilpotent and every pair $(\psi, P)$ consisting of an $\mathcal O$-algebra map $\psi : O^{nr} \to B$ and a Deligne datum $P$ over $B$ (a rule attaching to each full lattice $M \subseteq K_0^2$ a $B$-submodule of $B \otimes_{\mathcal O} M$ with invertible quotient, monotone in $M$, equivariant for homotheties and nondegenerate at every prime), a point of $\mathcal X$ over $\operatorname{Spec} B$, that is, a morphism $\operatorname{Spec} B \to \mathcal X$ whose composite with $f$ is $\operatorname{Spec}$ of the structure map $\mathcal O \to B$. Further, $D$ is a formal quotient datum for these parameters; among its fields are a tower of schemes $D.Y_n$ with proper structure morphisms $D.\mathrm{yb}_n : D.Y_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$, transition morphisms $D.\mathrm{yt}_n : D.Y_n \to D.Y_{n+1}$ making the squares with the base reductions cartesian, and a functorial family of points $D.q_n$ of $D.Y_n$ on $\mathcal O$-algebras $B$ with $\pi^{n+1} = 0$ in $B$, indexed by pairs $(\psi,P)$ as above, compatible with the transitions and invariant under the twisted action of $\Gamma$ (in which $\mathrm{Fr}$ and $v\det$ enter), together with the remaining fields of the structure, including its chart data.
--
--   Write $\bar\pi$ for the image of $\pi$ in $O^{nr}$, $O^{nr}_n := O^{nr}/(\bar\pi^{\,n+1})$ and $\mathcal O_n := \mathcal O/(\pi^{n+1})$; let $E :=$ `chartERing Onr` $\bar\pi$ $r$, the localisation of $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,2)\,O^{nr}$ modulo the relation `edgeRel` away from the discriminant element `edgeQuot.discr`, with its distinguished elements `chartERing.ξ` and `chartERing.η`, and put $A_n := E/(\bar\pi_E^{\,n+1})$, where $\bar\pi_E$ is the image of $\bar\pi$ in $E$.
--
--   The following data and hypotheses on bases and levels are assumed. Morphisms $s_n : \operatorname{Spec} O^{nr}_n \to \operatorname{Spec}\mathcal O$ with `hsn` identifying $s_n$ with $\operatorname{Spec}$ of the structure map $\mathcal O \to O^{nr}_n$; morphisms $t_n : \operatorname{Spec} O^{nr}_n \to \operatorname{Spec} O^{nr}_{n+1}$ with `htn` identifying $t_n$ with $\operatorname{Spec}$ of the reduction $O^{nr}_{n+1} \to O^{nr}_n$, and `htsn` asserting that $t_n$ followed by $s_{n+1}$ is $s_n$. Morphisms $j_n : \mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec} O^{nr}_n \to \mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec} O^{nr}_{n+1}$ between the fibre products (taken along $f$ and $s_n$, $s_{n+1}$) with `hjn₁`: $j_n$ followed by the first projection is the first projection, and `hjn₂`: $j_n$ followed by the second projection equals the second projection followed by $t_n$. Similarly morphisms $s^R_n : \operatorname{Spec}\mathcal O_n \to \operatorname{Spec}\mathcal O$ with `hsR` identifying them with $\operatorname{Spec}$ of $\mathcal O \to \mathcal O_n$, morphisms $t^R_n : \operatorname{Spec}\mathcal O_n \to \operatorname{Spec}\mathcal O_{n+1}$ subject only to `htR`, that $t^R_n$ followed by $s^R_{n+1}$ is $s^R_n$, and morphisms $x_n$ between the fibre products $\mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec}\mathcal O_n$ with the two compatibilities `hxn₁`, `hxn₂` analogous to `hjn₁`, `hjn₂` (with $t^R_n$ in place of $t_n$).
--
--   Finally, morphisms $v_n : D.Y_n \to \mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec}\mathcal O_n$ are given such that: `hv_over`, $v_n$ followed by the second projection is $D.\mathrm{yb}_n$; `hv_sq`, the square formed by $D.\mathrm{yt}_n$, $v_n$, $v_{n+1}$ and $x_n$ is cartesian; `hv_q`, for every $n$, every $\mathcal O$-algebra $B$ with $\pi^{n+1} = 0$ in $B$ and every pair $x = (\psi,P)$ as above, the composite of $D.q_n(B,x)$ with $v_n$ and the first projection is the underlying morphism of $\Theta_B(x)$; and `hv_iso`, each $v_n$ is an isomorphism.
--
--   Under these hypotheses there exist: for every $h \in \mathrm{GL}_2(K_0)$ and every $n$, an open subset $U_{h,n}$ of $\mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec} O^{nr}_n$; a ring homomorphism $c_{h,n} : \Gamma(U_{h,n}) \to A_n$ from the sections of the structure sheaf over $U_{h,n}$; and a morphism $\kappa_{h,n} : \operatorname{Spec} A_n \to \mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec} O^{nr}_n$, such that the following six assertions hold.
--
--   First, for all $h$ and $n$ the preimage $\kappa_{h,n}^{-1}(U_{h,n})$ is the whole of $\operatorname{Spec} A_n$, and for every section $s$ over $U_{h,n}$ the element $c_{h,n}(s)$ is obtained by applying $\kappa_{h,n}^{*}$ to $s$, restricting along $\top \le \kappa_{h,n}^{-1}(U_{h,n})$ and using the canonical identification of the global sections of $\operatorname{Spec} A_n$ with $A_n$; thus $c_{h,n}$ is the map on sections induced by $\kappa_{h,n}$.
--
--   Second, for all $h$, $n$ and all $y \in O^{nr}$: applying $c_{h,n}$ to the restriction to $U_{h,n}$ of the global function on the fibre product obtained by pulling back along the second projection the global function on $\operatorname{Spec} O^{nr}_n$ corresponding to $y \bmod \bar\pi^{\,n+1}$ yields the class of the image of $y$ in $A_n$.
--
--   Third, for all $h$ and $n$ one has $U_{h,n} = j_n^{-1}(U_{h,n+1})$, and for every section $s$ over $U_{h,n+1}$ the element $c_{h,n}$ of the restriction of $j_n^{*}s$ equals the image of $c_{h,n+1}(s)$ under the reduction $A_{n+1} \to A_n$.
--
--   Fourth, the charts compute the points supplied by $\Theta$: for all $h$, $n$, every commutative ring $B$ which is both an $\mathcal O$-algebra and an $O^{nr}$-algebra compatibly with $\mathcal O \to O^{nr}$ and in which the image of $\pi$ is nilpotent, every $O^{nr}$-algebra map $\bar x : A_n \to B$ and all Deligne data $d, P$ over $B$, if $d$ lies in the $g_1$-edge chart coordinatised by $\bar x$, that is, $d(\mathrm{std})$ is the $B$-span of $\bar x(\xi)\otimes e_0 + 1 \otimes e_1$ in $B \otimes_{\mathcal O}\mathrm{std}$, where $\mathrm{std}$ is the standard full lattice with basis vectors $e_0, e_1$, $d(g_1\cdot\mathrm{std})$ is the image under the base-changed action isomorphism of the $B$-span of $1 \otimes e_0 + \bar x(\eta)\otimes e_1$, and $d$ satisfies the edge-chart nondegeneracy condition `InEdgeChart` for the pair $(g_1\cdot\mathrm{std}, \mathrm{std})$ (at every prime $\mathfrak p$ of $B$: $g_1\cdot\mathrm{std} \subseteq \mathrm{std}$, $\pi\,\mathrm{std} \subseteq g_1\cdot\mathrm{std}$, and the indicated elements $1 \otimes v$ avoid the line plus $\mathfrak p$-part), and if moreover $P$ is the pullback of $d$ along $h^{-1}$, i.e. $P(M)$ is the preimage of $d(h^{-1}M)$ under the base-changed isomorphism for every full lattice $M$, then the underlying morphism of $\Theta_B(\text{canonical map } O^{nr}\to B, P)$ equals $\operatorname{Spec}\bar x$ followed by $\kappa_{h,n}$ followed by the first projection.
--
--   Fifth, for every $n$ the supremum of the $U_{h,n}$ over all $h \in \mathrm{GL}_2(K_0)$ is the whole fibre product.
--
--   Sixth, for every $h$ the maps $c_{h,m}$ identify the inverse limit of the $\Gamma(U_{h,m})$ with a subset of the inverse limit of the $A_m$, described as follows. Injectivity: if $s$ and $s'$ are families with $s_m, s'_m \in \Gamma(U_{h,m})$, each compatible with the transitions (the restriction of $j_m^{*}s_{m+1}$ is $s_m$, and likewise for $s'$), and if $c_{h,m}(s_m) = c_{h,m}(s'_m)$ for all $m$, then $s = s'$. Image: for every family $(\mathrm{fam}_m)_m$ with $\mathrm{fam}_m \in A_m$ compatible with the reductions $A_{m+1}\to A_m$, the existence of a transition-compatible family $(s_m)_m$ of sections with $c_{h,m}(s_m) = \mathrm{fam}_m$ for all $m$ is equivalent to the following $\Gamma'$-invariance: for every $m$, every $B$ that is an $\mathcal O$-algebra and an $O^{nr}$-algebra compatibly, with the image of $\pi$ nilpotent, all $O^{nr}$-algebra maps $\bar x, \bar x' : A_m \to B$ and all Deligne data $d, d', P, P'$ over $B$ such that $d$ lies in the $g_1$-edge chart coordinatised by $\bar x$ and $d'$ in the one coordinatised by $\bar x'$ (the same three conditions as in the fourth assertion), $P$ is the pullback of $d$ along $h^{-1}$, $P'$ is the pullback of $d'$ along $h^{-1}$, and there exists $\gamma \in \Gamma'$ with $P'$ the pullback of $P$ along $\sigma(\gamma)^{-1}$, one has $\bar x(\mathrm{fam}_m) = \bar x'(\mathrm{fam}_m)$.
--
--   This is the transport step in the Čerednik–Drinfeld part of the development: once the levels of a formal quotient datum are identified, by the isomorphisms $v_n$, with the reductions $\mathcal X \times_{\operatorname{Spec}\mathcal O}\operatorname{Spec}(\mathcal O/\pi^{n+1})$ of an $\mathcal O$-scheme $\mathcal X$ compatibly with the points produced by $\Theta$, the chartwise description of the formal completion after base change to $O^{nr}$ — edge charts covering each level, the induced maps on sections, their compatibility with the transitions, and the identification of compatible families of chart functions with $\Gamma'$-invariant families — is available for $\mathcal X$ itself. It is used by [`CerednikDrinfeld.exists_opens_chartMorphism_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_opens_chartMorphism_of_cerednikDrinfeld_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_opens_chartMorphism_of_formalQuotientDatum_of_isIso.lean

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.exists_opens_chartMorphism_of_formalQuotientDatum_of_isIso
    {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ Γ' : Subgroup G)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)

    (D : FormalQuotientDatum 𝒪 π K₀ Onr Fr vdet r σ Γ Γ' g₁)

    (sn : ∀ n : ℕ, Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪))
    (hsn : ∀ n : ℕ, sn n = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))))
    (tn : ∀ n : ℕ, Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1 + 1)})))
    (htn : ∀ n : ℕ, tn n = Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 Onr π) (Nat.le_succ (n + 1)))))))
    (htsn : ∀ n : ℕ, tn n ≫ sn (n + 1) = sn n)

    (jn : ∀ n : ℕ, Limits.pullback f (sn n) ⟶ Limits.pullback f (sn (n + 1)))
    (hjn₁ : ∀ n : ℕ, jn n ≫ Limits.pullback.fst f (sn (n + 1)) = Limits.pullback.fst f (sn n))
    (hjn₂ : ∀ n : ℕ, jn n ≫ Limits.pullback.snd f (sn (n + 1)) = Limits.pullback.snd f (sn n) ≫ tn n)

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (v : ∀ n : ℕ, D.Y n ⟶ Limits.pullback f (sR n))
    (hv_over : ∀ n : ℕ, v n ≫ Limits.pullback.snd f (sR n) = D.yb n)
    (hv_sq : ∀ n : ℕ, IsPullback (D.yt n) (v n) (v (n + 1)) (xn n))
    (hv_q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      D.q n B hB x ≫ v n ≫ Limits.pullback.fst f (sR n) = (Θ B ⟨n + 1, hB⟩ x).1)
    (hv_iso : ∀ n : ℕ, IsIso (v n)) :
    ∃ (U : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (Limits.pullback f (sn n)).Opens)
      (c : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
        ↑((Limits.pullback f (sn n)).presheaf.obj (Opposite.op (U h n))) →+* ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))
      (κ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Limits.pullback f (sn n)),

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (κ h n) ⁻¹ᵁ (U h n) = ⊤ ∧
        ∀ (hle : (⊤ : (Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).Opens) ≤ (κ h n) ⁻¹ᵁ (U h n))
          (s : ↑((Limits.pullback f (sn n)).presheaf.obj (Opposite.op (U h n)))),
          c h n s = (Scheme.ΓSpecIso (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).hom.hom
            ((Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).presheaf.map (homOfLE hle).op (((κ h n).app (U h n)).hom s))) ∧

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ) (y : Onr),
        c h n ((Limits.pullback f (sn n)).presheaf.map (homOfLE le_top).op
          ((Limits.pullback.snd f (sn n)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))).inv.hom
            (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) y)))) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) y)) ∧

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
        U h n = (jn n) ⁻¹ᵁ (U h (n + 1)) ∧
        ∀ (hle : U h n ≤ (jn n) ⁻¹ᵁ (U h (n + 1))) (s : ↑((Limits.pullback f (sn (n + 1))).presheaf.obj (Opposite.op (U h (n + 1))))),
          c h n ((Limits.pullback f (sn n)).presheaf.map (homOfLE hle).op (((jn n).app (U h (n + 1))).hom s)) =
          Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
            (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (n + 1)))) (c h (n + 1) s)) ∧

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
          (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          (Θ B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)).1 =
            Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ h n ≫ Limits.pullback.fst f (sn n)) ∧

      (∀ n : ℕ, ⨆ h : Matrix.GeneralLinearGroup (Fin 2) K₀, U h n = ⊤) ∧

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀),
        (∀ (s s' : ∀ m : ℕ, ↑((Limits.pullback f (sn m)).presheaf.obj (Opposite.op (U h m)))),
          (∀ (m : ℕ) (hle : U h m ≤ (jn m) ⁻¹ᵁ (U h (m + 1))),
              (Limits.pullback f (sn m)).presheaf.map (homOfLE hle).op (((jn m).app (U h (m + 1))).hom (s (m + 1))) = s m) →
          (∀ (m : ℕ) (hle : U h m ≤ (jn m) ⁻¹ᵁ (U h (m + 1))),
              (Limits.pullback f (sn m)).presheaf.map (homOfLE hle).op (((jn m).app (U h (m + 1))).hom (s' (m + 1))) = s' m) →
          (∀ m : ℕ, c h m (s m) = c h m (s' m)) → s = s') ∧
        ∀ fam : ∀ m : ℕ, ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}), (∀ m : ℕ, Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (m + 1)))) (fam (m + 1)) = fam m) →
          ((∃ s : ∀ m : ℕ, ↑((Limits.pullback f (sn m)).presheaf.obj (Opposite.op (U h m))),
              (∀ (m : ℕ) (hle : U h m ≤ (jn m) ⁻¹ᵁ (U h (m + 1))),
              (Limits.pullback f (sn m)).presheaf.map (homOfLE hle).op (((jn m).app (U h (m + 1))).hom (s (m + 1))) = s m) ∧
              ∀ m : ℕ, c h m (s m) = fam m) ↔
            ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B],
              IsNilpotent (algebraMap 𝒪 B π) →
              ∀ (xbar xbar' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B) (d d' P P' : DeligneDatum (K := K₀) π B),
                (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                (d'.line (stdFullLattice K₀) =
              Submodule.span B {(xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d' P' →
                (∃ γ ∈ Γ', DeligneDatum.IsPullback (K := K₀) (π := π) B (σ γ)⁻¹ P P') →
                xbar (fam m) = xbar' (fam m))) := by sorry
