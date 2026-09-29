-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one
-- name    : AutomorphicForm.exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/5fb5d5d6-3818-5a27-9893-738f892be408
-- title:
--   Hyperbolic class sums as finite sums of twisted lattice sums
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, and for every finite place $v$ of $K$ a prime $w_v =$ `ws v` of $\mathcal{O}_L$ lying under $v$ is fixed (an element of `v.Extension (𝓞 L)`, that is, a height-one prime of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$). The group $(\mathbb{A}_K)^\times$ of unit ideles carries a measurable structure which is the Borel structure of its topology, and $\nu_{Z_K}$ is a Haar measure on it. For a finite place $v$, [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) denotes the set of $g \in \mathrm{GL}_2(K_v)$ such that all entries of $g$ and of $g^{-1}$ lie in the valuation ring of $K_v$; [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) is the Haar measure on $\mathrm{GL}_2(K_v)$ normalised to give this compact open set mass one, and `adelicGLHaar (Fin 2) (𝓞 K) K` is Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$. For an idele unit $z$, [`AutomorphicForm.centralScalar (𝓞 K) K z`](def/AutomorphicForm_AdelicLsXi.html#L18) is the scalar matrix $z \cdot 1$, and `diagUnits2 x y` is $\mathrm{diag}(x,y)$; the elements of interest are $\gamma_{u,z} = z\cdot\mathrm{diag}(u,1)$ for $u \in K^\times$ embedded diagonally in the ideles.
--
--   Data and hypotheses.
--
--   (i) Characters. $\Xi$ is a finite set of homomorphisms from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$. The hypothesis `hΞc` requires each $\xi \in \Xi$ to be continuous as a $\mathbb{C}$-valued function of the idele, `hΞt` requires $\xi$ to be trivial on the image of $K^\times$, and `hur` requires, for $\xi \in \Xi$ and $v \notin S_K$, that $\xi$ kill the idele which is a given $t \in (K_v)^\times$ of valuation $1$ at $v$ and $1$ elsewhere.
--
--   (ii) Places. $S_K$ and $T$ are finite sets of finite places of $K$; `hTS` says $T$ and $S_K$ are disjoint and `hT2` that $T$ has at least two elements.
--
--   (iii) Norms and Satake parameters. $N_w : v \mapsto$ `Nw v` is a natural-number-valued function with `hNw`: for $v \in T$, `Nw v` is the absolute norm of the ideal $w_v$, and `hNwf`: for $v \in T$, `Nw v` $=$ $(\mathrm{N}v)^{f_v}$ where $f_v =$ [`AutomorphicForm.SatakeCombination.slotDeg K L ws v`](def/AutomorphicForm_SatakeCombinationCoeff.html#L20) is the inertia degree of $w_v$ over $v$. Further $\zeta, s$ are $\mathbb{C}$-valued functions on finite places with `hζ`: $\zeta_v \neq 0$ for $v \in T$, `hs`: $s_v^2 = \zeta_v$ for $v \in T$, and `hx`: for every $\xi \in \Xi$ and $v \in T$, $\xi(\det(\mathrm{heckeGen}_v))^{f_v} = \zeta_v$, where `heckeGen (𝓞 K) K v` is the element $\mathrm{diag}(\varpi_v,1)$ built from a uniformiser at $v$.
--
--   (iv) Test functions. $f_{a,K}$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ satisfies `IsArchTestFactor`: it has compact support and is of the form $g \mapsto \Phi$ applied to the matrix of entries of $g$ transported into the mixed space of $K$, for some $\Phi$ of class $C^\infty$. For each finite place $v$ a function $f_{S_K,v}$ on $\mathrm{GL}_2(K_v)$ is given, and `hfSK` requires $f_{S_K,v}$ to be locally constant with compact support for $v \in S_K$. Two real constants $\kappa_{0,K}, \kappa_K$ are given, without further hypotheses; they occur as factors on the left-hand side.
--
--   (v) Global factorisation. $\nu_A$ is a measure on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ for the Borel structure `glBorelOf`, and $c_G$ a real constant. The hypothesis `hG` states: for every finite set $S$ of finite places, every $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, every $f_a$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and every family $(f_S{}_{,v})_v$ of local functions such that $f_a$ is a.e. strongly measurable for $\nu_A$, each $f_{S,v}$ ($v \in S$) is a.e. strongly measurable for `localHaar K v`, $f(g)$ equals $f_a(g_\infty)\prod_{v \in S} f_{S,v}(g_v)$ whenever every component $g_v$ with $v \notin S$ lies in `localIntegralSet K v`, and $f(g) = 0$ whenever some component $g_v$ with $v \notin S$ does not, one has $\int f \, d(\text{adelic Haar}) = c_G \cdot (\int f_a \, d\nu_A) \cdot \prod_{v \in S} \int f_{S,v} \, d(\text{local Haar})$.
--
--   (vi) Torus measures. A constant $c_{\tau K} > 0$ (`hcτK`) is given together with, for each $u \in K^\times$ and each idele unit $z$, a measure $\tau_G(u,z)$ on the centraliser of $\{\gamma_{u,z}\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$; `hτG` requires it to be Haar and `hτGc` requires, for $u \neq 1$ in $K$, that $\int_{\text{centraliser}} g(t)\, d\tau_G(u,z) = c_{\tau K} \int g(\mathrm{diag}(p_1,p_2)) \, d(\nu_{Z_K}\times\nu_{Z_K})$ for every $g$. Likewise measures $\tau_A(u,z)$ on the centraliser of the archimedean component of $\gamma_{u,z}$ (Borel structure `centralizerBorel`) and $\tau_F(u,z,v)$ on the centraliser of the $v$-component of the finite part of $\gamma_{u,z}$ (Borel structure `localCentralizerBorel`) are given; `hτA` and `hτF` require them to be Haar for $u \neq 1$, and `hτF1` normalises $\tau_F(u,z,v)$ so that the preimage of `localIntegralSet K v` has mass $1$. A constant $c_T > 0$ (`hcT`) and the hypothesis `hT` provide the corresponding factorisation on centralisers: for $u \neq 1$, any $z$, any finite $S$ and any $W$, $W_a$, $(W_{S,v})_v$ subject to the same measurability, product and vanishing conditions as in `hG` (now with respect to $\tau_A(u,z)$, $\tau_F(u,z,v)$ and `localIntegralSet`), $\int W \, d\tau_G(u,z) = c_T \cdot (\int W_a \, d\tau_A(u,z)) \cdot \prod_{v\in S} \int W_{S,v} \, d\tau_F(u,z,v)$.
--
--   (vii) Product-measure datum. $P_Z$ is a [`UnramifiedWhittaker.ProductMeasureData SK νZK`](def/UnramifiedWhittaker_ZetaIntegrand.html#L20): a positive constant `PZ.c`, a measure `PZ.νS` on unit ideles, an endomorphism `PZ.projS` of the unit idele group, a function `PZ.ord`, and the axioms of that structure — that `projS a` has trivial finite component outside $S_K$, that every unit idele outside $S_K \cup L$ factors as `projS a` times a product of uniformiser ideles to the exponents `ord v a` times an everywhere-integral unit idele, a Tonelli formula expressing integrals over `unitIdelesOutside (𝓞 K) K (S_K ∪ L)` as `PZ.c` times $\int f \, d\nu_S$ times a product of sums $\sum_{m\in\mathbb{Z}}\varphi_v(m)$, and measurability of the sets involved. The compatibilities `hPo`, `hPp`, `hPν` require `PZ.ord` to be the valuation-order function [`NumberField.Idele.ord K`](def/NumberField_IdeleProductMeasure.html#L13), `PZ.projS` to be the truncation [`NumberField.Idele.partAt K SK`](def/NumberField_IdeleProductMeasure.html#L90) to $S_K$, and $\mathrm{ofReal}(P_Z.c) \cdot P_Z.\nu_S$ to be the pushforward under `partAt K SK` of $\nu_{Z_K}$ restricted to the unit ideles that are integral, with integral inverse, outside $S_K$.
--
--   (viii) Orbital integrals. $I_A : K^\times \times (\mathbb{A}_K)^\times \to \mathbb{C}$ and $I_F : K^\times \times (\mathbb{A}_K)^\times \times \{\text{places}\} \to \mathbb{C}$ satisfy `hIA` and `hIF`: for $u \neq 1$ in $K$, $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at the archimedean component of $\gamma_{u,z}$ for $\nu_A$ and $\tau_A(u,z)$ in the sense of `IsOrbitalIntegralOn` (there is a non-negative measurable compactly supported weight $w$ with $\int_{\text{centraliser}} w(tx) \, d\tau_A = 1$ whenever $f_{a,K}(x^{-1}\gamma x) \neq 0$, and $I_A(u,z) = \int f_{a,K}(x^{-1}\gamma x) w(x) \, d\nu_A$), and for $v \in S_K$, $I_F(u,z,v)$ is the analogous local orbital integral of $f_{S_K,v}$ at the $v$-component of the finite part of $\gamma_{u,z}$ for `localHaar K v` and $\tau_F(u,z,v)$.
--
--   Conclusion. Write $r = \#\,\mathrm{InfinitePlace}(K)$ and $m = \#T$, and let $v_i =$ `T.equivFin.symm i` denote the $i$-th place of $T$. Then there exist: a natural number $N$; an additive subgroup $\Lambda \le (\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,m \to \mathbb{Z})$ carrying the discrete topology; a real-linear form $sl$ on $\mathrm{Fin}\,r \to \mathbb{R}$ and a non-zero $\omega \in \mathbb{R}^m$ such that $sl(\gamma_1) = \sum_i \omega_i \gamma_{2,i}$ for every $\gamma \in \Lambda$; an additive homomorphism $\chi : \Lambda \to (\mathrm{Fin}(r+m) \to \mathbb{R}/\mathbb{Z})$ together with a map $\mathrm{lift}$ from $(\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,m \to \mathbb{Z})$ to $\mathrm{Fin}(r+m) \to \mathbb{R}$ whose reduction modulo $1$ in each coordinate $j$ agrees with $\chi(\gamma)_j$ for every $\gamma \in \Lambda$; subgroups $\mathrm{sub}(i) \le \Lambda$ for $i \in \mathrm{Fin}\,N$; functions $G_i$ on $(\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}(r+m) \to \mathbb{R})$ of class $C^\infty$; a real $R_b \ge 0$ such that $G_i(p) = 0$ whenever $|p_{1,k}| > R_b$ for some $k$, and such that each $G_i$ is invariant under $p_2 \mapsto p_2 + e_j$ for every coordinate $j$; and shifts $x_0(i) \in \mathrm{Fin}\,r \to \mathbb{R}$, $n_0(i) \in \mathrm{Fin}\,m \to \mathbb{Z}$, $\theta_0(i) \in \mathrm{Fin}(r+m) \to \mathbb{R}$, with the following property.
--
--   For every $n : \mathrm{Fin}\,m \to \mathbb{Z}$,
--   $$\big(\kappa_{0,K}\,\kappa_K\,(c_G\, c_T^{-1}\, P_Z.c)\big) \sum^{\mathrm{f}}_{u} \Big(\prod_{i} \big(\sqrt{N_w(v_i)}\, s_{v_i}\big)^{-n_i}\Big)\cdot A(u) \cdot \sum_{\xi \in \Xi} \int \xi(z_S)\, \big(I_A(u,z_S) \prod_{v \in S_K} I_F(u,z_S,v)\big)\, dP_Z.\nu_S = \sum_{i=1}^{N} \ \sum_{\gamma \in \mathrm{sub}(i)} \begin{cases} G_i\big(x_0(i) + \gamma_1,\ \theta_0(i) + \mathrm{lift}(\gamma)\big) & \text{if } \gamma_2 + n_0(i) = n,\\ 0 & \text{otherwise,}\end{cases}$$
--   where the left-hand sum is the finitely supported sum over the set of $u \in K^\times$ with $(u : K) \neq 1$ such that [`NumberField.Idele.ord K v`](def/NumberField_IdeleProductMeasure.html#L13) of the principal idele of $u$ vanishes for every finite place $v \notin S_K \cup T$, and such that for each $i$ the order of the principal idele of $u$ at $v_i$ equals $f_{v_i} \cdot n_i$; where $A(u)$ is the module $\mathrm{ideleNorm}_K\big(\mathrm{partAt}_{S_K}(u-1)\big)$ of the $S_K$-truncation of the principal idele of $u - 1$, taken to be $0$ in case $u - 1 = 0$; and the right-hand inner sum is an unconditional sum over the countable group $\mathrm{sub}(i)$.
--
--   This is the passage, in the comparison of trace formulae underlying base change for $\mathrm{GL}(2)$, from sums over hyperbolic (split regular) conjugacy classes of $K$ indexed by Hecke words at the places of $T$ to a finite sum of lattice sums of smooth windows, periodic in the angle variables and compactly supported in the logarithmic variables. It is used by the construction of the winding datum, [`AutomorphicForm.exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted`](thm.html#AutomorphicForm.exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted), from which the analytic estimates on the hyperbolic contribution are extracted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]

    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞc : ∀ ξ ∈ Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hΞt : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK) (hT2 : 2 ≤ T.card)

    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNw : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal = Nw v)
    (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ v)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (κ₀K κK : ℝ)

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))

    (cτK : ℝ) (hcτK : 0 < cτK)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))

    (PZ : UnramifiedWhittaker.ProductMeasureData SK νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K SK)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS =
      Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v)) :
    ∃ (N : ℕ) (Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), DiscreteTopology Λ ∧
      ∃ (sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ) (ω : Fin T.card → ℝ), ω ≠ 0 ∧
        (∀ γ ∈ Λ, sl γ.1 = ∑ i, ω i * (γ.2 i : ℝ)) ∧
      ∃ (χ : Λ →+ (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → AddCircle (1 : ℝ)))
        (lift : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        (∀ (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) (hγ : γ ∈ Λ) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∃ (sub : Fin N → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), (∀ i, sub i ≤ Λ) ∧
      ∃ (G : Fin N → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ), (∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) ∧
      ∃ (Rb : ℝ), 0 ≤ Rb ∧
        (∀ i (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), (∃ k, Rb < |p.1 k|) → G i p = 0) ∧
        (∀ i (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)), G i (p.1, p.2 + Pi.single j 1) = G i p) ∧
      ∃ (x₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) (n₀ : Fin N → Fin T.card → ℤ) (θ₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
      ∀ n : Fin T.card → ℤ,
        ((κ₀K : ℂ) * ((κK : ℝ) : ℂ) * ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ)) *
          ∑ᶠ u ∈ {u : Kˣ | (u : K) ≠ 1 ∧
              (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ∧
              ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
                (AutomorphicForm.SatakeCombination.slotDeg K L ws (T.equivFin.symm i).1 : ℤ) * n i},
            (∏ i : Fin T.card, (((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ (-(n i)))) *
            (if h1 : (u : K) - 1 ≠ 0 then
                ((NumberField.TateGlobal.ideleNorm K
                    (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
              else 0) *
            ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
                (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS =
        ∑ i : Fin N, ∑' γ : sub i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ i = n then
            G i (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0 := by sorry
