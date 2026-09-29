-- Prove2me | Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen
-- name    : AlgebraicGeometry.TowerQuotientDatum.exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/70526a1c-e101-55a7-89a9-c11e5ebdf23c
-- title:
--   A flat model A' for the base-changed chart ring
-- statement:
--   Throughout, $\mathcal O$ is a commutative domain which is a discrete valuation ring, $\pi \in \mathcal O$ an irreducible element, and $\mathcal O$ is assumed $(\pi)$-adically complete. Write $\mathcal O_n := \mathcal O/(\pi^{n+1})$.
--
--   **The tower and its group action.** A family of schemes $X_n$ ($n \in \mathbb N$) is given together with structure morphisms $xb_n : X_n \to \operatorname{Spec} \mathcal O_n$ and transition morphisms $xt_n : X_n \to X_{n+1}$, subject to: `hcart`, each square formed by $xt_n$, $xb_n$, $xb_{n+1}$ and $\operatorname{Spec}$ of the reduction $\mathcal O_{n+1} \to \mathcal O_n$ is cartesian; `hproper` and `hflat`, each $xb_n$ is proper and flat; `haff`, every finite subset of $X_n$ lies in an affine open of $X_n$. A finite group $G$ acts through homomorphisms $a_n : G \to \operatorname{Aut}(X_n)$, with `ha_over` each $a_n(g)$ a morphism over $\operatorname{Spec}\mathcal O_n$, and `ha_xt` the actions compatible with the transitions.
--
--   **The quotient datum.** $D$ is a `TowerQuotientDatum` for these data: it provides schemes $Y_n$ with structure morphisms $yb_n : Y_n \to \operatorname{Spec}\mathcal O_n$ and transitions $yt_n : Y_n \to Y_{n+1}$ whose squares against the reductions $\mathcal O_{n+1} \to \mathcal O_n$ are cartesian, each $yb_n$ proper and flat; morphisms $p_n : X_n \to Y_n$ over $\operatorname{Spec}\mathcal O_n$ (i.e. $p_n$ followed by $yb_n$ is $xb_n$), compatible with the transitions ($xt_n$ followed by $p_{n+1}$ equals $p_n$ followed by $yt_n$, and the square formed by $xt_n, p_n, p_{n+1}, yt_n$ is cartesian), $G$-invariant ($a_n(g)$ followed by $p_n$ is $p_n$), finite and surjective, with $p_n$ restricted over any open of $Y_n$ an epimorphism; and a local universal property `univ_loc` presenting $Y_n$, over any compatible system of opens, as the quotient of $X_n$ by $G$ for $G$-invariant families of morphisms to a test scheme compatible with the transitions.
--
--   **Base change along a flat $\mathcal O$-algebra.** $S$ is a commutative $\mathcal O$-algebra, flat as an $\mathcal O$-module; put $S_n := S/(\pi_S^{n+1})$ with $\pi_S := \operatorname{algebraMap}_{\mathcal O \to S}(\pi)$. Schemes $X'_n$ with structure morphisms $xb'_n : X'_n \to \operatorname{Spec} S_n$, transitions $xt'_n$, $G$-actions $a'_n$ and morphisms $q_n : X'_n \to X_n$ are given, subject to: `hq`, the square formed by $q_n$, $xb'_n$, $xb_n$ and $\operatorname{Spec}$ of the induced map $\mathcal O_n \to S_n$ is cartesian; `hcart'`, the analogous transition squares for $xt'_n$ over the reductions $S_{n+1} \to S_n$ are cartesian; `hq_xt` and `hq_a`, $q$ is compatible with the transitions and with the $G$-actions; `ha'_over`, each $a'_n(g)$ is a morphism over $\operatorname{Spec} S_n$.
--
--   **The base-changed quotient tower.** Schemes $Y'_n$ with $yb'_n : Y'_n \to \operatorname{Spec} S_n$, transitions $yt'_n$, morphisms $p'_n : X'_n \to Y'_n$ and $r_n : Y'_n \to D.Y_n$ are given, subject to: `hbase`, the square formed by $r_n$, $yb'_n$, $D.yb_n$ and $\operatorname{Spec}(\mathcal O_n \to S_n)$ is cartesian; `hsq`, the square formed by $q_n$, $p'_n$, $D.p_n$, $r_n$ is cartesian; `hyt'r` and `hyt'b`, $yt'$ is compatible with $r$ and with the base reductions; `hp'_over`, $p'_n$ followed by $yb'_n$ is $xb'_n$; `hp'_inv`, $p'_n$ is $G$-invariant; `hp'_xt`, $p'$ is compatible with the transitions.
--
--   **Affine charts and the chart ring $R$.** Affine opens $V_n \subseteq D.Y_n$ are given with $yt_n^{-1}(V_{n+1}) = V_n$ (`hVa`, `hV`). $R$ is a commutative $\mathcal O$-algebra carrying a multiplicative semiring action of $G$ commuting with the $\mathcal O$-scalars, which is $(\pi_R)$-adically complete (`hRc`), has no $\pi_R$-torsion (`hRtf`, where $\pi_R$ is the image of $\pi$), and with $R/\pi_R R$ of finite type over $\mathcal O$ (`hRft`). Writing $A :=$ `FixedPoints.subalgebra 𝒪 R G` for the $\mathcal O$-subalgebra of $G$-invariants, ring isomorphisms
--   $$\mathrm{lvl}_n : R/(\pi_R^{n+1}) \xrightarrow{\ \sim\ } \Gamma(X_n, p_n^{-1}V_n), \qquad \mu_n : A/(\pi_A^{n+1}) \xrightarrow{\ \sim\ } \Gamma(Y_n, V_n)$$
--   are given, subject to the compatibilities: `hlvl_xt`, restriction along $xt_n$ carries $\mathrm{lvl}_{n+1}(\bar x)$ to $\mathrm{lvl}_n(\bar x)$; `hlvl_smul`, the map on sections induced by $a_n(g^{-1})$ carries $\mathrm{lvl}_n(\bar x)$ to $\mathrm{lvl}_n(\overline{g\cdot x})$; `hlvl_xb`, $\mathrm{lvl}_n$ of the image of $o \in \mathcal O$ is the pullback along $xb_n$ of the global section of $\operatorname{Spec}\mathcal O_n$ corresponding to $\bar o$; `hμ_yt`, restriction along $yt_n$ carries $\mu_{n+1}(\bar x)$ to $\mu_n(\bar x)$; `hμ_p`, pullback along $p_n$ carries $\mu_n(\bar x)$ to $\mathrm{lvl}_n(\overline{x})$ for $x \in A$ viewed in $R$; `hμ_yb`, $\mu_n$ of the image of $o \in \mathcal O$ is the pullback along $yb_n$ of the section corresponding to $\bar o$.
--
--   **The element $b$ and the maps $\varphi_n$.** An element $b \in A \otimes_{\mathcal O} S$ is given, together with additive maps $\varphi_n : A \otimes_{\mathcal O} S \to \Gamma(Y'_n, r_n^{-1}V_n)$ such that (`hφ`) on pure tensors $\varphi_n(x \otimes s)$ is the product of the pullback along $r_n$ of $\mu_n(\bar x)$ with the pullback along $yb'_n$ of the global section of $\operatorname{Spec} S_n$ corresponding to $\bar s$; each $\varphi_n$ is surjective (`hφs`); and (`hV'`) $yt_n'^{-1}$ of the basic open $D(\varphi_{n+1}(b)) \subseteq Y'_{n+1}$ equals $D(\varphi_n(b)) \subseteq Y'_n$.
--
--   **The primed chart ring $R'$.** $R'$ is a commutative $S$-algebra with a multiplicative semiring action of $G$ commuting with the $S$-scalars, $(\pi_{R'})$-adically complete (`hR'c`) and without $\pi_{R'}$-torsion (`hR'tf`), where $\pi_{R'}$ is the image of $\pi_S$, together with ring isomorphisms
--   $$\mathrm{lvl}'_n : R'/(\pi_{R'}^{n+1}) \xrightarrow{\ \sim\ } \Gamma\bigl(X'_n, p_n'^{-1}D(\varphi_n(b))\bigr)$$
--   subject to: `hlvl'_xt`, compatibility with restriction along $xt'_n$; `hlvl'_smul`, the map on sections induced by $a'_n(g^{-1})$ carries $\mathrm{lvl}'_n(\bar x)$ to $\mathrm{lvl}'_n(\overline{g \cdot x})$; `hlvl'_xb`, $\mathrm{lvl}'_n$ of the image of $s \in S$ is the pullback along $xb'_n$ of the section corresponding to $\bar s$.
--
--   **Conclusion.** There exist a commutative ring $A'$, an $A$-algebra structure on $A'$ which is flat as an $A$-module, a ring homomorphism $\sigma : S \to A'$, and families of ring isomorphisms
--   $$\tau_n : \bigl(R \otimes_A A'\bigr)\big/\bigl(\pi_R^{n+1} \otimes 1\bigr) \xrightarrow{\ \sim\ } R'/(\pi_{R'}^{n+1}), \qquad \theta_n : A'/(\sigma(\pi_S)^{n+1}) \xrightarrow{\ \sim\ } \Gamma\bigl(Y'_n, D(\varphi_n(b))\bigr),$$
--   such that all of the following hold:
--
--   1. $\sigma$ is a map of $\mathcal O$-algebras: for every $o \in \mathcal O$, $\sigma$ of the image of $o$ in $S$ equals the image in $A'$ of the image of $o$ in $A$.
--
--   2. The $\tau_n$ are compatible with the levels in the following form: for all $n$, $z \in R \otimes_A A'$ and $y \in R'$, if $\tau_{n+1}(\bar z) = \bar y$ then $\tau_n(\bar z) = \bar y$.
--
--   3. Equivariance on pure tensors: for all $n$, $g \in G$, $x \in R$, $w \in A'$ and $y \in R'$, if $\tau_n(\overline{x \otimes w}) = \bar y$ then $\tau_n(\overline{(g\cdot x) \otimes w}) = \overline{g \cdot y}$.
--
--   4. For all $n$ and $s \in S$, $\tau_n(\overline{1 \otimes \sigma(s)})$ is the class of the image of $s$ in $R'$.
--
--   5. The $\theta_n$ are compatible with the transitions: restriction along $yt'_n$ from $D(\varphi_{n+1}(b))$ to $D(\varphi_n(b))$ carries $\theta_{n+1}(\bar w)$ to $\theta_n(\bar w)$ for every $w \in A'$.
--
--   6. The $\theta_n$ are compatible with the structure maps: for all $n$ and $s \in S$, $\theta_n(\overline{\sigma(s)})$ is the pullback along $yb'_n$ of the global section of $\operatorname{Spec} S_n$ corresponding to $\bar s$.
--
--   7. The $\theta_n$ and $\mathrm{lvl}'_n$ match through $p'_n$: for all $n$, $w \in A'$ and $y \in R'$, if $\tau_n(\overline{1 \otimes w}) = \bar y$ then the pullback along $p'_n$ of $\theta_n(\bar w)$ equals $\mathrm{lvl}'_n(\bar y)$.
--
--   This is the algebraic reading of the base-changed chart of a tower quotient datum: the basic open $D(\varphi_n(b)) \subseteq Y'_n$ and its preimage in $X'_n$ are presented by a single flat $A$-algebra $A'$ with a compatible system of level isomorphisms, $A$ being the ring of $G$-invariants of the chart ring $R$. It is proved by combining [`AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_quotient_sections_preimage_and_basicOpen`](thm.html#AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_quotient_sections_preimage_and_basicOpen) with [`AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_tensorProduct_quotient_of_ringEquiv_sections_basicOpen`](thm.html#AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_tensorProduct_quotient_of_ringEquiv_sections_basicOpen), and is used in [`AlgebraicGeometry.TowerQuotientDatum.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen`](thm.html#AlgebraicGeometry.TowerQuotientDatum.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TowerQuotientDatum_exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen.lean

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

theorem AlgebraicGeometry.TowerQuotientDatum.exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen
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
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A') (_ : Module.Flat ↥(FixedPoints.subalgebra 𝒪 R G) A')
      (σ : S →+* A')
      (τ : ∀ n : ℕ, ((R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') ⧸
          Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ≃+*
        (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}))
      (θ : ∀ n : ℕ, (A' ⧸ Ideal.span {σ (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+* Γ(Y' n, ((Y' n).basicOpen (φ n b)))),

      (∀ o : 𝒪, σ (algebraMap 𝒪 S o) = algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) A' (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) ∧

      (∀ (n : ℕ) (z : R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') (y : R'),
        τ (n + 1) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y → τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y) ∧
      (∀ (n : ℕ) (g : G) (x : R) (w : A') (y : R'),
        τ n (Ideal.Quotient.mk _ (x ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
        τ n (Ideal.Quotient.mk _ ((g • x) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (g • y)) ∧
      (∀ (n : ℕ) (s : S),
        τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] σ s)) = Ideal.Quotient.mk _ (algebraMap S R' s)) ∧

      (∀ (n : ℕ) (w : A'), (yt' n).appLE ((Y' (n + 1)).basicOpen (φ (n + 1) b)) ((Y' n).basicOpen (φ n b)) (by rw [hV'])
          (θ (n + 1) (Ideal.Quotient.mk _ w)) = θ n (Ideal.Quotient.mk _ w)) ∧
      (∀ (n : ℕ) (s : S), θ n (Ideal.Quotient.mk _ (σ s)) =
          (yb' n).appLE ⊤ ((Y' n).basicOpen (φ n b)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
      (∀ (n : ℕ) (w : A') (y : R'), τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
          (p' n).appLE ((Y' n).basicOpen (φ n b)) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_rfl (θ n (Ideal.Quotient.mk _ w)) = lvl' n (Ideal.Quotient.mk _ y)) := by sorry
