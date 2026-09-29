-- Prove2me | Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen
-- name    : AlgebraicGeometry.TowerQuotientDatum.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/e45df56e-fdd3-5c60-821f-5fdd0b6ab1da
-- title:
--   Invariants of the base-changed chart ring: completeness and levels
-- statement:
--   Throughout, $\mathcal O$ is a commutative domain which is a discrete valuation ring (`hdvr`), $\pi \in \mathcal O$ is irreducible (`hπ`) and $\mathcal O$ is complete for the $\pi$-adic topology (`hcomplete`); write $\mathcal O_n := \mathcal O/(\pi^{n+1})$, and for an $\mathcal O$-algebra $T$ write $\pi_T$ for the image of $\pi$ in $T$.
--
--   **The tower $X$.** A family of schemes $X_n$ ($n \in \mathbb N$) is given together with morphisms $xb_n : X_n \to \operatorname{Spec} \mathcal O_n$ and transition morphisms $xt_n : X_n \to X_{n+1}$. The hypotheses on this tower are: `hcart`, each square formed by $xt_n$, $xb_n$, $xb_{n+1}$ and the morphism $\operatorname{Spec} \mathcal O_n \to \operatorname{Spec} \mathcal O_{n+1}$ induced by the projection $\mathcal O_{n+1} \to \mathcal O_n$ is a pullback; `hproper` and `hflat`, each $xb_n$ is proper and flat; and `haff`, every finite subset of $X_n$ is contained in an affine open. A finite group $G$ is given with group homomorphisms $a_n : G \to \operatorname{Aut}(X_n)$ satisfying `ha_over`, $a_n(g)$ followed by $xb_n$ equals $xb_n$, and `ha_xt`, $a_n(g)$ followed by $xt_n$ equals $xt_n$ followed by $a_{n+1}(g)$.
--
--   **The quotient datum.** $D$ is a `TowerQuotientDatum` for these data: it consists of schemes $D.Y_n$ with structure morphisms $D.yb_n : D.Y_n \to \operatorname{Spec}\mathcal O_n$ and transitions $D.yt_n$ whose squares over $\operatorname{Spec}\mathcal O_n \to \operatorname{Spec}\mathcal O_{n+1}$ are pullbacks, each $D.yb_n$ proper and flat, together with morphisms $D.p_n : X_n \to D.Y_n$ satisfying $D.p_n$ followed by $D.yb_n$ equal to $xb_n$, the compatibility $xt_n \ggg D.p_{n+1} = D.p_n \ggg D.yt_n$ (in diagrammatic order), cartesianness of the square $xt_n$, $D.p_n$, $D.p_{n+1}$, $D.yt_n$, the $G$-invariance $a_n(g)$ followed by $D.p_n$ equals $D.p_n$, finiteness and surjectivity of $D.p_n$, epimorphy of the restriction of $D.p_n$ over every open of $D.Y_n$, and a local universal property `univ_loc` for $G$-invariant morphisms out of the opens $D.p_n^{-1}(U_n)$ for compatible families of opens $U_n$, along with the structure's remaining compatibility fields.
--
--   **Flat base change along $S$.** $S$ is a commutative $\mathcal O$-algebra, flat as an $\mathcal O$-module; set $S_n := S/(\pi_S^{\,n+1})$. Schemes $X'_n$ are given with $xb'_n : X'_n \to \operatorname{Spec} S_n$, transitions $xt'_n$, actions $a'_n : G \to \operatorname{Aut}(X'_n)$ and morphisms $q_n : X'_n \to X_n$, subject to: `hq`, the square $q_n$, $xb'_n$, $xb_n$ over $\operatorname{Spec} S_n \to \operatorname{Spec}\mathcal O_n$ (induced by $\mathcal O_n \to S_n$) is a pullback; `hcart'`, the squares $xt'_n$, $xb'_n$, $xb'_{n+1}$ over $\operatorname{Spec} S_n \to \operatorname{Spec} S_{n+1}$ are pullbacks; `hq_xt`, $xt'_n$ followed by $q_{n+1}$ equals $q_n$ followed by $xt_n$; `hq_a`, $q_n$ is $G$-equivariant; `ha'_over`, $a'_n(g)$ followed by $xb'_n$ equals $xb'_n$.
--
--   Similarly schemes $Y'_n$ are given with $yb'_n : Y'_n \to \operatorname{Spec} S_n$, transitions $yt'_n$, morphisms $p'_n : X'_n \to Y'_n$ and $r_n : Y'_n \to D.Y_n$, subject to: `hbase`, the square $r_n$, $yb'_n$, $D.yb_n$ over $\operatorname{Spec} S_n \to \operatorname{Spec}\mathcal O_n$ is a pullback; `hsq`, the square $q_n$, $p'_n$, $D.p_n$, $r_n$ is a pullback (so $X'_n = X_n \times_{D.Y_n} Y'_n$); `hyt'r`, $yt'_n$ followed by $r_{n+1}$ equals $r_n$ followed by $D.yt_n$; `hyt'b`, $yt'_n$ followed by $yb'_{n+1}$ equals $yb'_n$ followed by $\operatorname{Spec}$ of the projection $S_{n+1} \to S_n$; `hp'_over`, $p'_n$ followed by $yb'_n$ equals $xb'_n$; `hp'_inv`, $a'_n(g)$ followed by $p'_n$ equals $p'_n$; `hp'_xt`, $xt'_n$ followed by $p'_{n+1}$ equals $p'_n$ followed by $yt'_n$.
--
--   **Chart rings on the unprimed tower.** Opens $V_n \subseteq D.Y_n$ are given which are affine (`hVa`) and compatible, $D.yt_n^{-1}(V_{n+1}) = V_n$ (`hV`). A commutative $\mathcal O$-algebra $R$ is given carrying a $G$-action by ring automorphisms commuting with the $\mathcal O$-structure, such that $R$ is $\pi_R$-adically complete (`hRc`), $\pi_R$ is a non-zero-divisor on $R$ (`hRtf`), and $R/(\pi_R)$ is of finite type over $\mathcal O$ (`hRft`). Write $A :=$ `FixedPoints.subalgebra 𝒪 R G`, the $\mathcal O$-subalgebra of $G$-invariants of $R$. Ring isomorphisms are given
--   $$lvl_n : R/(\pi_R^{\,n+1}) \;\xrightarrow{\ \sim\ }\; \Gamma(X_n, D.p_n^{-1}(V_n)), \qquad \mu_n : A/(\pi_A^{\,n+1}) \;\xrightarrow{\ \sim\ }\; \Gamma(D.Y_n, V_n),$$
--   subject to the compatibilities: `hlvl_xt`, the restriction map along $xt_n$ from $D.p_{n+1}^{-1}(V_{n+1})$ to $D.p_n^{-1}(V_n)$ carries $lvl_{n+1}(\bar x)$ to $lvl_n(\bar x)$; `hlvl_smul`, the map on sections of $D.p_n^{-1}(V_n)$ induced by the automorphism $a_n(g^{-1})$ carries $lvl_n(\bar x)$ to $lvl_n(\overline{g\cdot x})$; `hlvl_xb`, for $o \in \mathcal O$, $lvl_n$ of the class of the image of $o$ in $R$ is the pullback along $xb_n$ of the global section of $\operatorname{Spec}\mathcal O_n$ corresponding to the class of $o$; `hμ_yt`, the restriction along $D.yt_n$ from $V_{n+1}$ to $V_n$ carries $\mu_{n+1}(\bar x)$ to $\mu_n(\bar x)$; `hμ_p`, the pullback along $D.p_n$ of $\mu_n(\bar x)$ is $lvl_n$ of the class of $x$ viewed in $R$; `hμ_yb`, the analogue of `hlvl_xb` for $\mu_n$ and $D.yb_n$.
--
--   **The element $b$ and the maps $\varphi_n$.** An element $b \in A \otimes_{\mathcal O} S$ is given, together with additive maps $\varphi_n : A \otimes_{\mathcal O} S \to \Gamma(Y'_n, r_n^{-1}(V_n))$ such that (`hφ`) $\varphi_n(x \otimes s)$ is the product of the pullback along $r_n$ of $\mu_n(\bar x)$ with the pullback along $yb'_n$ of the global section of $\operatorname{Spec} S_n$ corresponding to the class of $s$; each $\varphi_n$ is surjective (`hφs`); and the basic opens are compatible: $yt'^{-1}_n\bigl((Y'_{n+1})_{\varphi_{n+1}(b)}\bigr) = (Y'_n)_{\varphi_n(b)}$ (`hV'`).
--
--   **The primed chart ring.** $R'$ is a commutative $S$-algebra carrying a $G$-action by ring automorphisms commuting with the $S$-structure, such that $R'$ is adically complete for the ideal generated by the image of $\pi_S$ (`hR'c`) and that image is a non-zero-divisor on $R'$ (`hR'tf`). Ring isomorphisms are given
--   $$lvl'_n : R'/(\pi_{R'}^{\,n+1}) \;\xrightarrow{\ \sim\ }\; \Gamma\bigl(X'_n, p'^{-1}_n((Y'_n)_{\varphi_n(b)})\bigr)$$
--   satisfying the three compatibilities `hlvl'_xt` (with the restriction maps along $xt'_n$), `hlvl'_smul` (the map induced by $a'_n(g^{-1})$ carries $lvl'_n(\bar x)$ to $lvl'_n(\overline{g \cdot x})$) and `hlvl'_xb` (for $s \in S$, $lvl'_n$ of the class of the image of $s$ in $R'$ is the pullback along $xb'_n$ of the section of $\operatorname{Spec} S_n$ corresponding to the class of $s$).
--
--   **Conclusion.** Write $A'' :=$ `FixedPoints.subalgebra S R' G`, the $S$-subalgebra of $G$-invariants of $R'$, and let $\pi_{A''}$ denote the image of $\pi_S$ in $A''$. Then:
--
--   (i) $A''$ is adically complete for the ideal generated by $\pi_{A''}$; and
--
--   (ii) there exists a family of ring isomorphisms
--   $$\mu'_n : A''/(\pi_{A''}^{\,n+1}) \;\xrightarrow{\ \sim\ }\; \Gamma\bigl(Y'_n, (Y'_n)_{\varphi_n(b)}\bigr)$$
--   such that, for all $n$: the restriction map along $yt'_n$ from $(Y'_{n+1})_{\varphi_{n+1}(b)}$ to $(Y'_n)_{\varphi_n(b)}$ carries $\mu'_{n+1}(\bar x)$ to $\mu'_n(\bar x)$ for every $x \in A''$; the pullback along $p'_n$ of $\mu'_n(\bar x)$ to $p'^{-1}_n((Y'_n)_{\varphi_n(b)})$ equals $lvl'_n$ of the class of $x$ viewed in $R'$, for every $x \in A''$; and for every $s \in S$, $\mu'_n$ of the class of the image of $s$ in $A''$ is the pullback along $yb'_n$ of the global section of $\operatorname{Spec} S_n$ corresponding to the class of $s$.
--
--   This is the invariant-theoretic half of the base-change step for towers of proper flat schemes over a complete discrete valuation ring with a finite group action: it transports a chart description of the quotient tower (affine opens $V_n$ with invariant chart ring $A = R^G$) across a flat base change $\mathcal O \to S$ and a localisation at an element $b$, producing the corresponding chart ring $R'^G$ on the basic opens $(Y'_n)_{\varphi_n(b)}$ together with its levels and its $\pi$-adic completeness. It combines the purely algebraic statement that taking $G$-invariants commutes with the relevant flat base change with the identification of sections over the base-changed quotient charts, and it is used by [`AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_fixedPoints_quotient_basicOpen_of_isPullback_of_flat`](thm.html#AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_fixedPoints_quotient_basicOpen_of_isPullback_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TowerQuotientDatum_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen.lean

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

theorem AlgebraicGeometry.TowerQuotientDatum.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)

    (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S]
    (X' : ℕ → Scheme.{0}) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)) (a' : ∀ n : ℕ, G →* Aut (X' n))
    (q : ∀ n : ℕ, X' n ⟶ X n)
    (hq : ∀ n : ℕ, IsPullback (q n) (xb' n) (xb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1))))))))
    (hq_xt : ∀ n : ℕ, xt' n ≫ q (n + 1) = q n ≫ xt n)
    (hq_a : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom)
    (ha'_over : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n)

    (Y' : ℕ → Scheme.{0})
    (yb' : ∀ n : ℕ, Y' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (yt' : ∀ n : ℕ, Y' n ⟶ Y' (n + 1)) (p' : ∀ n : ℕ, X' n ⟶ Y' n) (r : ∀ n : ℕ, Y' n ⟶ D.Y n)
    (hbase : ∀ n : ℕ, IsPullback (r n) (yb' n) (D.yb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hsq : ∀ n : ℕ, IsPullback (q n) (p' n) (D.p n) (r n))
    (hyt'r : ∀ n : ℕ, yt' n ≫ r (n + 1) = r n ≫ D.yt n)
    (hyt'b : ∀ n : ℕ, yt' n ≫ yb' (n + 1) = yb' n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))
    (hp'_over : ∀ n : ℕ, p' n ≫ yb' n = xb' n)
    (hp'_inv : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ p' n = p' n)
    (hp'_xt : ∀ n : ℕ, xt' n ≫ p' (n + 1) = p' n ≫ yt' n)
    (V : ∀ n : ℕ, (D.Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
    (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n)
    (R : Type) [CommRing R] [Algebra 𝒪 R] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)))
    (μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
      Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n))
    (hlvl_xt : ∀ (n : ℕ) (x : R), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
        (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
        (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x))
    (hlvl_smul : ∀ (n : ℕ) (g : G) (x : R), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
        (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
        lvl n (Ideal.Quotient.mk _ (g • x)))
    (hlvl_xb : ∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
        (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)))
    (hμ_yt : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
        (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x))
    (hμ_p : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl
        (μ n (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ (x : R)))
    (hμ_yb : ∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) =
        (D.yb n).appLE ⊤ (V n) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)))
    (b : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)

    (φ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) →+ Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
    (hφ : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)) (s : S), φ n (x ⊗ₜ[𝒪] s) =
        (r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl (μ n (Ideal.Quotient.mk _ x)) *
        (yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))
    (hφs : ∀ n : ℕ, Function.Surjective (φ n))
    (hV' : ∀ n : ℕ, (yt' n) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b)) = (Y' n).basicOpen (φ n b))

    (R' : Type) [CommRing R'] [Algebra S R'] [MulSemiringAction G R'] [SMulCommClass G S R']
    (hR'c : IsAdicComplete (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) R')
    (hR'tf : ∀ x : R', algebraMap S R' (algebraMap 𝒪 S π) * x = 0 → x = 0)
    (lvl' : ∀ n : ℕ, (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
      Γ(X' n, (p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))))
    (hlvl'_xt : ∀ (n : ℕ) (x : R'), (xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV'])
        (lvl' (n + 1) (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ x))
    (hlvl'_smul : ∀ (n : ℕ) (g : G) (x : R'), (a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) (lvl' n (Ideal.Quotient.mk _ x)) =
        lvl' n (Ideal.Quotient.mk _ (g • x)))
    (hlvl'_xb : ∀ (n : ℕ) (s : S), lvl' n (Ideal.Quotient.mk _ (algebraMap S R' s)) =
        (xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) :
    IsAdicComplete (Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π)}) ↥(FixedPoints.subalgebra S R' G) ∧
    ∃ (μ' : ∀ n : ℕ, (↥(FixedPoints.subalgebra S R' G) ⧸ Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
        Γ(Y' n, ((Y' n).basicOpen (φ n b)))),
      (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra S R' G)), (yt' n).appLE ((Y' (n + 1)).basicOpen (φ (n + 1) b)) ((Y' n).basicOpen (φ n b)) (by rw [hV'])
          (μ' (n + 1) (Ideal.Quotient.mk _ x)) = μ' n (Ideal.Quotient.mk _ x)) ∧
      (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra S R' G)), (p' n).appLE ((Y' n).basicOpen (φ n b)) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_rfl
          (μ' n (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ (x : R'))) ∧
      (∀ (n : ℕ) (s : S), μ' n (Ideal.Quotient.mk _ (algebraMap S ↥(FixedPoints.subalgebra S R' G) s)) =
          (yb' n).appLE ⊤ ((Y' n).basicOpen (φ n b)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) := by sorry
