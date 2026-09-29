-- Prove2me | Theorems.Thm_AutomorphicForm_exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted
-- name    : AutomorphicForm.exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0bdbce6b-4573-5fdb-8bd1-4d721fd684ed
-- title:
--   The K-side class sum as a winding-datum coefficient array
-- statement:
--   Data. Two number fields $K$ and $L$ with an algebra map $K \to L$ are fixed, together with a choice `ws` assigning to every finite place $v$ of $K$ an extension of $v$ to $\mathcal{O}_L$, i.e. a height-one prime $(\mathrm{ws}\,v)_1$ of $\mathcal{O}_L$ lying under $v$; and a Haar measure $\nu_{Z,K}$ on the group of idele units $(\mathbb{A}_K)^\times = (\mathrm{AdeleRing}\,\mathcal{O}_K\,K)^\times$, whose measurable structure is the Borel structure of its topology.
--
--   Character data. $\Xi$ is a finite set of monoid homomorphisms from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$. The hypotheses on it are: `hΞc`, each $\xi \in \Xi$ is continuous as a $\mathbb{C}$-valued function of the idele $z$; `hΞt`, each $\xi \in \Xi$ is trivial on the image of $K^\times$ under the principal-idele map; and `hur`, for $\xi \in \Xi$, for every place $v \notin S_K$ and every $t \in (K_v)^\times$ with $|t|_v = 1$, the value of $\xi$ at the idele which is $t$ at $v$ and $1$ elsewhere (built with `localUnit` and `finIncl`) is $1$.
--
--   Place data. $S_K$ and $T$ are finite sets of finite places of $K$, with `hTS` asserting that $T$ and $S_K$ are disjoint and `hT2` that $2 \le \#T$.
--
--   Norm and Satake data. $N_w : \mathrm{places} \to \mathbb{N}$ satisfies `hNw`: for $v \in T$, $N_w(v)$ is the absolute norm of the ideal of $(\mathrm{ws}\,v)_1$; and `hNwf`: for $v \in T$, $N_w(v) = (\mathrm{absNorm}\,v)^{f_v}$, where $f_v =$ `SatakeCombination.slotDeg K L ws v` is the inertia degree of $v$ in $(\mathrm{ws}\,v)_1$. Functions $\zeta, s : \mathrm{places} \to \mathbb{C}$ satisfy `hζ`: $\zeta_v \ne 0$ for $v \in T$; `hs`: $s_v^2 = \zeta_v$ for $v \in T$; and `hx`: for every $\xi \in \Xi$ and $v \in T$, the value of $\xi$ at the determinant of `heckeGen (𝓞 K) K v` (the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of the uniformiser unit at $v$) raised to the power $f_v$ equals $\zeta_v$.
--
--   Test functions. $f_{a,K}$ is a function on $\mathrm{GL}_2$ of the infinite adele ring of $K$ with `hfaK`: `IsArchTestFactor`, i.e. there is a $C^\infty$ function $\Phi$ on matrices of entries in the mixed space of $K$ with $f_{a,K}(g) = \Phi(\mathrm{archEntries}\,g)$, and $f_{a,K}$ has compact support. For each finite place $v$, $f_{S_K}(v)$ is a function on $\mathrm{GL}_2(K_v)$, and `hfSK` requires, for $v \in S_K$, that it be locally constant with compact support. Two real constants $\kappa_0$ and $\kappa$ are fixed, with no hypotheses.
--
--   Global factorisation of the adelic Haar integral. A measure $\nu_A$ on $\mathrm{GL}_2$ of the infinite adele ring (for the Borel structure `glBorelOf`) and a real constant $c_G$ are fixed, and `hG` asserts: for every finite set $S$ of finite places and all functions $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $f_a$ on the archimedean group and $f_S(v)$ on the local groups, subject to almost-everywhere strong measurability of $f_a$ for $\nu_A$ and of each $f_S(v)$, $v \in S$, for the local Haar measure `localHaar K v`, if $f(g) = f_a(g_\infty) \cdot \prod_{v \in S} f_S(v)(g_v)$ whenever every component of $g$ outside $S$ lies in `localIntegralSet K v` (the set of $\mathrm{GL}_2$ elements whose matrix and inverse matrix have entries in $\mathcal{O}_{K_v}$), and $f(g) = 0$ whenever some component outside $S$ fails to lie in that set, then $\int f \, d(\mathrm{adelicGLHaar})= c_G \cdot (\int f_a \, d\nu_A) \cdot \prod_{v \in S} \int f_S(v) \, d(\mathrm{localHaar}\,K\,v)$.
--
--   Centraliser measures. Write $\gamma(u,z) = z \cdot \mathrm{diag}(u,1)$ for the product of the central scalar attached to an idele unit $z$ with the diagonal element `diagUnits2` of the principal idele of $u \in K^\times$ and $1$. A constant $c_{\tau,K} > 0$ is fixed (`hcτK`), together with: $\tau_G(u,z)$, a measure on the centraliser of $\{\gamma(u,z)\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$, Haar whenever $u \ne 1$ in $K$ (`hτG`), and satisfying `hτGc`, that for $u \ne 1$ and every $g : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ the $\tau_G(u,z)$-integral of $g$ over that centraliser equals $c_{\tau,K}$ times the $\nu_{Z,K} \times \nu_{Z,K}$-integral of $g(\mathrm{diag}(p_1,p_2))$; $\tau_A(u,z)$, a measure for the Borel structure `centralizerBorel` on the centraliser of the archimedean component of $\gamma(u,z)$, Haar for $u \ne 1$ (`hτA`); and $\tau_F(u,z,v)$, a measure for `localCentralizerBorel` on the local centraliser of the $v$-component of the finite part of $\gamma(u,z)$, Haar for $u \ne 1$ (`hτF`) and of total mass $1$ on the preimage of `localIntegralSet K v` (`hτF1`). A constant $c_T > 0$ is fixed (`hcT`), and `hT` asserts the corresponding factorisation on centralisers: for $u \ne 1$, any $z$, any finite set $S$ and functions $W$, $W_a$, $W_S$ with almost-everywhere strong measurability of $W_a$ for $\tau_A(u,z)$ and of each $W_S(v)$, $v \in S$, for $\tau_F(u,z,v)$, if $W(t) = W_a(t_\infty)\cdot\prod_{v \in S} W_S(v)(t_v)$ whenever all components of $t$ off $S$ are in `localIntegralSet K v`, and $W(t) = 0$ whenever some component off $S$ is not, then $\int W \, d\tau_G(u,z) = c_T \cdot (\int W_a \, d\tau_A(u,z)) \cdot \prod_{v \in S} \int W_S(v) \, d\tau_F(u,z,v)$.
--
--   Product measure data. $P_Z$ is a term of [`UnramifiedWhittaker.ProductMeasureData SK νZK`](def/UnramifiedWhittaker_ZetaIntegrand.html#L20), packaging a constant $P_Z.c > 0$, a measure $P_Z.\nu_S$ on the idele units, a monoid endomorphism $P_Z.\mathrm{projS}$, an order function $P_Z.\mathrm{ord}$, and the structural conditions `projS_off`, `decomp`, `tonelli` and `measurableSet` relating them on the subgroups `unitIdelesOutside`. Three hypotheses pin this data down: `hPo`, $P_Z.\mathrm{ord}$ is [`NumberField.Idele.ord K`](def/NumberField_IdeleProductMeasure.html#L13); `hPp`, $P_Z.\mathrm{projS}$ is [`NumberField.Idele.partAt K SK`](def/NumberField_IdeleProductMeasure.html#L90), the endomorphism keeping the archimedean component and the components at places of $S_K$ and setting the other finite components to $1$; and `hPν`, that $P_Z.c \cdot P_Z.\nu_S$ is the push-forward under that endomorphism of $\nu_{Z,K}$ restricted to the subgroup of idele units that are integral, together with their inverses, at all places outside $S_K$.
--
--   Orbital integrals. $I_A : K^\times \to (\mathbb{A}_K)^\times \to \mathbb{C}$ satisfies `hIA`: for $u \ne 1$ and any $z$, $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at the archimedean component of $\gamma(u,z)$ for $\nu_A$ and $\tau_A(u,z)$, that is, there is a non-negative measurable compactly supported weight $w$ with $\int_{\mathrm{centraliser}} w(tx)\, d\tau_A(u,z) = 1$ for every $x$ with $f_{a,K}(x^{-1}\gamma x) \ne 0$, and $I_A(u,z) = \int f_{a,K}(x^{-1}\gamma x)\,w(x)\,d\nu_A$. Likewise $I_F : K^\times \to (\mathbb{A}_K)^\times \to \mathrm{places} \to \mathbb{C}$ satisfies `hIF`: for $u \ne 1$, any $z$ and $v \in S_K$, $I_F(u,z,v)$ is the analogous orbital integral of $f_{S_K}(v)$ at the $v$-component of the finite part of $\gamma(u,z)$, taken against `localHaar K v` and $\tau_F(u,z,v)$.
--
--   Conclusion. There exists a winding datum $\mathcal{A}$ of signature $(r,d,c)$ with $r = \#\{\text{infinite places of } K\}$, $d = \#T$ and $c = r + d$ — that is, a term of [`AutomorphicForm.WindingDatum`](def/AutomorphicForm_WindingDatum.html#L11), which packages a discrete subgroup $\Lambda \le (\mathbb{R}^r \times \mathbb{Z}^d)$, a linear form $s$ on $\mathbb{R}^r$ and a non-zero weight vector $\omega \in \mathbb{R}^d$ with $s(x_1) = \sum_i \omega_i x_{2,i}$ on $\Lambda$, a homomorphism $\chi : \Lambda \to (\mathbb{R}/\mathbb{Z})^c$, subgroups $\mathrm{sub}\,i \le \Lambda$, continuous integrable functions $\Psi_i$ on $\mathbb{R}^r$ with quadratic-decay bounds $C_i \prod_k (1+|x_k|)^{-2}$ for $\Psi_i$ and for its Fourier transform, and further shift data ($m$, $\theta_0$, $x_0$ and the remaining fields), whose coefficient array is $\mathcal{A}.\mathrm{coeff}\,n = \sum_{i \in \mathbb{N}} \mathcal{A}.\mathrm{lam}\,i \cdot \mathcal{A}.\mathrm{fibreCoeff}\,i\,n$ with $\mathcal{A}.\mathrm{fibreCoeff}\,i\,n$ the sum of $\mathcal{A}.\mathrm{fibreTerm}\,i\,n\,\gamma$ over $\gamma \in \mathrm{sub}\,i$ — such that for every $n : \mathrm{Fin}\,\#T \to \mathbb{Z}$,
--   $$\mathcal{A}.\mathrm{coeff}\,n = \kappa_0\,\kappa\,(c_G\,c_T^{-1}\,P_Z.c)\sum^{\mathrm{f}}_{u \in U_n} \Big(\prod_{i} \big(\sqrt{N_w(v_i)}\; s_{v_i}\big)^{-n_i}\Big)\cdot D(u) \cdot \sum_{\xi \in \Xi}\int \xi(z_S)\,\Big(I_A(u,z_S)\prod_{v \in S_K} I_F(u,z_S,v)\Big)\, dP_Z.\nu_S ,$$
--   where: the sum is the finsum over the set $U_n$ of those $u \in K^\times$ with $u \ne 1$ in $K$, with $\mathrm{ord}_v$ of the principal idele of $u$ equal to $0$ for every place $v \notin S_K$ with $v \notin T$, and with $\mathrm{ord}_{v_i}$ of the principal idele of $u$ equal to $f_{v_i}\, n_i$ for every index $i$, the place $v_i$ being the $i$-th element of $T$ under `T.equivFin.symm` and $f_{v_i}$ its slot degree; the factor $D(u)$ is given by the dependent case distinction: if $u - 1 \ne 0$ in $K$ then $D(u)$ is the real idele norm [`NumberField.TateGlobal.ideleNorm K`](def/NumberField_TateGlobalZeta.html#L19) (the value of the distributive Haar character) of `Idele.partAt K SK` applied to the principal idele of $u-1$, and $D(u) = 0$ otherwise; and each power $(\sqrt{N_w(v_i)}\,s_{v_i})^{-n_i}$ is an integer power in $\mathbb{C}$, with $\sqrt{\cdot}$ the real square root of $N_w(v_i)$ coerced to $\mathbb{C}$.
--
--   This is the packaging step on the $K$-side of a comparison of trace formulae: the sum over regular split (hyperbolic) rational classes $u \in K^\times$, weighted by the tilt factors $(\sqrt{N_w}\,s_v)^{-n_i}$, the discriminant idele norm of the $S_K$-and-archimedean part of $u-1$, and the character window $\sum_{\xi \in \Xi}\int \xi \cdot (I_A \prod_{v \in S_K} I_F)$, is exhibited as the coefficient array of a winding datum, so that the lattice, periodicity and decay structure of that array becomes available. It is obtained from the unfolding of the class sum together with the existence theorem for winding data from smooth, compactly supported, periodic fibre functions, and it feeds the Satake-Laurent identification of the $K$-side and $L$-side arrays.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted.lean

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

theorem AutomorphicForm.exists_windingDatum_forall_coeff_eq_mul_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_of_smul_eq_map_partAt_of_ne_one_unweighted
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
    ∃ 𝒜 : AutomorphicForm.WindingDatum (Fintype.card (NumberField.InfinitePlace K)) T.card
        (Fintype.card (NumberField.InfinitePlace K) + T.card), ∀ n : Fin T.card → ℤ, 𝒜.coeff n =
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
              (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS := by sorry
