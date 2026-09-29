-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalQuotientDatum_isIso_of_isPullback_of_cerednikDrinfeld_quotient
-- name    : CerednikDrinfeld.FormalQuotientDatum.isIso_of_isPullback_of_cerednikDrinfeld_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/3cbacc7f-2d14-52d1-99fc-db507d830c6e
-- title:
--   Formal quotient datum comparison maps are isomorphisms
-- statement:
--   Fix a natural number $r$, a commutative ring $\mathcal O$ with an element $\pi$, a field $K_0$ that is an $\mathcal O$-algebra, a commutative $\mathcal O$-algebra $O^{\mathrm{nr}}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, a monoid homomorphism $v\!\det : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively), a group $G$ with a homomorphism $\sigma : G \to \mathrm{GL}_2(K_0)$, subgroups $\Gamma, \Gamma' \le G$, an element $g_1 \in \mathrm{GL}_2(K_0)$, and a scheme $\mathcal X$ with a morphism $f : \mathcal X \to \operatorname{Spec}\mathcal O$. The datum $\Theta$ assigns, to every $\mathcal O$-algebra $B$ in which the image of $\pi$ is nilpotent, a map from pairs $(\psi, d)$ with $\psi : O^{\mathrm{nr}} \to_{\mathcal O} B$ an $\mathcal O$-algebra homomorphism and $d$ a Deligne datum over $B$ (the value at $B$ of `Omega K₀ π`) to the set of morphisms $\operatorname{Spec} B \to \mathcal X$ over $\operatorname{Spec}\mathcal O$; `hΘnat` says $\Theta$ commutes with base change along $\mathcal O$-algebra maps, `hΘinv` says $\Theta$ takes equal values on pairs $x, x'$ related by the twisted action of $\sigma\gamma$ for $\gamma \in \Gamma$, i.e. with $x'_1 = \mathrm{Fr}^{-v\!\det(\sigma\gamma)}$-twist of $x_1$ and $x'_2$ the pullback of $x_2$ along $(\sigma\gamma)^{-1}$, and `hΘuniv` asserts the corresponding categorical quotient property: for every $\mathcal O$-scheme $t : T \to \operatorname{Spec}\mathcal O$ and every natural, twisted-$\Gamma$-invariant family $\rho'$ of such pairs into the $\pi$-nilpotent points of $T$, there is a natural family $u$ of maps from the $\pi$-nilpotent points of $f$ to those of $t$ with $u \circ \Theta = \rho'$, and any natural $u'$ with this property agrees with $u$ pointwise. Let $D$ be a `FormalQuotientDatum` for these parameters, with schemes $D.Y\,n$, structure morphisms $D.yb\,n : D.Y\,n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ which are proper, cartesian transition maps $D.yt\,n$, and the quotient maps $D.q\,n$. Let $sR\,n$ be the morphisms $\operatorname{Spec}(\mathcal O/\pi^{n+1}) \to \operatorname{Spec}\mathcal O$ induced by the quotient maps, $tR\,n : \operatorname{Spec}(\mathcal O/\pi^{n+1}) \to \operatorname{Spec}(\mathcal O/\pi^{n+2})$ morphisms with $sR(n+1) \circ tR\,n = sR\,n$, and $x_n$ morphisms between the truncations $\mathcal X_n := \mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec}(\mathcal O/\pi^{n+1})$ compatible with both projections (second projection composed with $tR\,n$). Suppose given morphisms $v_n : D.Y\,n \to \mathcal X_n$ with $v_n$ followed by the projection to $\operatorname{Spec}(\mathcal O/\pi^{n+1})$ equal to $D.yb\,n$, such that each square $(D.yt\,n, v_n, v_{n+1}, x_n)$ is cartesian and such that $D.q\,n\,B\,h_B\,x$ followed by $v_n$ and the projection to $\mathcal X$ is the morphism underlying $\Theta\,B\,x$, for every $B$ with $(\pi\cdot 1_B)^{n+1} = 0$. Suppose finally the system algebraises: there are a scheme $Y_f$, a morphism $G_f : Y_f \to \mathcal X$ and morphisms $\varphi_n : D.Y\,n \to Y_f$ compatible with the $D.yt\,n$ such that each square $(\varphi_n, v_n, G_f, \mathcal X_n \to \mathcal X)$ is cartesian. Then $v_n$ is an isomorphism for every $n$.
--
--   This is the inversion step in the Čerednik–Drinfeld comparison: the categorical quotient property of $\Theta$ on $\pi$-nilpotent points, together with algebraisation of the tower, forces the comparison morphisms from a formal quotient datum to the $\pi$-adic truncations of the quotient scheme to be isomorphisms. It is used by [`CerednikDrinfeld.exists_opens_chartMorphism_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_opens_chartMorphism_of_cerednikDrinfeld_quotient) and [`CerednikDrinfeld.forall_exists_adicPoint_and_theta_eq_iff_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.forall_exists_adicPoint_and_theta_eq_iff_of_cerednikDrinfeld_quotient), and its proof cites the gluing statement [`AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_of_natural`](thm.html#AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_of_natural).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalQuotientDatum_isIso_of_isPullback_of_cerednikDrinfeld_quotient.lean

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalQuotientDatum.isIso_of_isPullback_of_cerednikDrinfeld_quotient
    {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ Γ' : Subgroup G)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘuniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
          u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (Θ B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
            u' B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (Θ B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f).obj B),
            u' B hB y = u B hB y)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)

    (D : FormalQuotientDatum 𝒪 π K₀ Onr Fr vdet r σ Γ Γ' g₁)

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

    (Yf : Scheme.{0}) (Gf : Yf ⟶ 𝒳) (φ : ∀ n : ℕ, D.Y n ⟶ Yf)
    (hφ : ∀ n : ℕ, IsPullback (φ n) (v n) Gf (Limits.pullback.fst f (sR n)))
    (hφt : ∀ n : ℕ, D.yt n ≫ φ (n + 1) = φ n) :
    ∀ n : ℕ, IsIso (v n) := by sorry
