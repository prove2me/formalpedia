-- Prove2me | Theorems.Thm_AutomorphicForm_isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
-- name    : AutomorphicForm.isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/e61ad99d-57f4-5d60-bf00-f4f9055004f3
-- title:
--   Local constancy and integrability of the split-family window product
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ a finite Galois extension, $\sigma \in \mathrm{Gal}(L/K)$ is an element such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (hypothesis `hgen`), and $[L:K] = \operatorname{finrank}_K L$ is prime (`hprime`). The group $(\mathbb{A}_K)^\times$ of ideles carries a measurable structure which is the Borel structure of its topology, and $\nu_{Z_K}$ is a Haar measure on it. Two finite sets $S_K, T$ of maximal ideals of $\mathcal{O}_K$ are given, with $T$ disjoint from $S_K$ (`hTS`).
--
--   For $u \in K^\times$ and $z \in (\mathbb{A}_K)^\times$ write $\gamma(u,z) = \mathrm{centralScalar}(z) \cdot \mathrm{diagUnits2}(u_{\mathbb{A}},1) \in \mathrm{GL}_2(\mathbb{A}_K)$, the diagonal matrix with entries $z u$ and $z$ (here $u_{\mathbb{A}}$ is the image of $u$ under `Units.map` of $K \to \mathbb{A}_K$), and let $\gamma_\infty(u,z) = \mathrm{glArch}\,\gamma(u,z)$ and $\gamma_v(u,z) = \mathrm{finComponent}_v(\mathrm{glFin}\,\gamma(u,z))$ be its archimedean and $v$-components.
--
--   *Test data.* $f_{a,K}$ is an archimedean test factor for $K$ (`IsArchTestFactor`: it is $\Phi \circ \mathrm{archEntries}$ for some $C^\infty$ function $\Phi$ on matrices over the mixed space of $K$, and has compact support); $f_{S_K}$ assigns to each finite place a function on $\mathrm{GL}_2(K_v)$ which for $v \in S_K$ is locally constant with compact support (`IsLocalTestFn`); $\varphi_a$ is an archimedean test factor for $L$; $\varphi_S$ assigns to each $v$ a function on $\mathrm{GL}_2(L \otimes_K K_v)$ which for $v \in S_K$ is locally constant with compact support (`IsSemiLocalTestFn`); $f_T$ assigns to each $v$ a function on $\mathrm{GL}_2(K_v)$ which for $v \in T$ is a local test function.
--
--   *Global splitting of Haar measure.* A measure $\nu_A$ on $\mathrm{GL}_2$ of the infinite adeles of $K$ (for the Borel structure `glBorelOf`) and a real constant $c_G$ are given, together with the hypothesis `hG`: for every finite set $S$ of finite places and all $f, f_a, f_S$ such that $f_a$ is a.e. strongly measurable for $\nu_A$, each $f_S(v)$ ($v \in S$) is a.e. strongly measurable for the local Haar measure `localHaar`, $f(g) = f_a(g_\infty)\prod_{v \in S} f_S(v)(g_v)$ whenever all components $g_v$ for $v \notin S$ lie in the integral set $\mathrm{localIntegralSet}$ (matrices with both $g_v$ and $g_v^{-1}$ integral), and $f(g) = 0$ as soon as some $g_v$, $v \notin S$, is not in that set, one has $\int f \, d(\mathrm{adelicGLHaar}) = c_G \cdot (\int f_a \, d\nu_A) \cdot \prod_{v \in S} \int f_S(v) \, d(\mathrm{localHaar})$.
--
--   *Centralizer measures and their splitting.* A constant $c_{\tau K} > 0$, measures $\tau_G(u,z)$ on the centralizer of $\{\gamma(u,z)\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$ which are Haar for $u \neq 1$ (`hτG`) and satisfy, for $u \neq 1$ and every complex-valued function $g$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $\int_{\mathrm{cent}} g \, d\tau_G(u,z) = c_{\tau K}\int g(\mathrm{diagUnits2}(p_1,p_2)) \, d(\nu_{Z_K} \times \nu_{Z_K})$ (`hτGc`); measures $\tau_A(u,z)$ on the centralizer of $\gamma_\infty(u,z)$, Haar for $u \neq 1$; measures $\tau_F(u,z,v)$ on the local centralizer of $\gamma_v(u,z)$, Haar for $u \neq 1$ and of total mass $1$ on the preimage of $\mathrm{localIntegralSet}$ (`hτF1`); and a constant $c_T > 0$ with the hypothesis `hT`: for $u \neq 1$, every finite $S$ and all $W, W_a, W_S$ satisfying the corresponding measurability, factorisation and vanishing conditions on the adelic centralizer, $\int W \, d\tau_G(u,z) = c_T \cdot (\int W_a \, d\tau_A(u,z)) \cdot \prod_{v \in S}\int W_S(v) \, d\tau_F(u,z,v)$.
--
--   *Orbital integrals over $K$.* For $u \neq 1$: $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at $\gamma_\infty(u,z)$ for $\nu_A$ and $\tau_A(u,z)$, i.e. $I_A = \int f_{a,K}(x^{-1}\gamma_\infty x) w(x) \, d\nu_A$ for some non-negative measurable compactly supported $w$ with $\int w(tx) \, d\tau_A = 1$ whenever $f_{a,K}(x^{-1}\gamma_\infty x) \neq 0$; $I_F(u,z,v)$ ($v \in S_K$) is the analogous local orbital integral of $f_{S_K}(v)$ at $\gamma_v(u,z)$ against `localHaar` and $\tau_F(u,z,v)$; $J_A(u,z)$ is the weighted orbital integral of $f_{a,K}$ with the archimedean weight $y \mapsto -\log \mathrm{archHeight}_K(y) - \log \mathrm{archHeight}_K(w_\infty y)$, where $w_\infty$ is the archimedean component of the adelic Weyl element $\mathrm{adelicWeyl}$; $J_F(u,z,v)$ ($v \in S_K$) is the weighted local orbital integral of $f_{S_K}(v)$ with the weight `LocalWeight.weight`.
--
--   *Twisted data.* $\nu_A'$ is a measure on $\mathrm{GL}_2(L \otimes_K (\text{infinite adeles of } K))$, and $\nu_A = \mathrm{archHaarK}$, $\nu_A' = \mathrm{archHaarL}$ (`hνA`, `hνA'`). Elements $\delta_A(u,z)$ are given whose norm string $\prod_{i<[L:K]} \sigma_{\mathrm{GL}}^{i}(\delta_A(u,z))$ equals $\mathrm{toTensorGL}(\gamma_\infty(u,z))$ whenever $\gamma_\infty(u,z)$ is a norm in the twisted sense `IsNormOf` (`hδA`), together with measures $\tau_A'(u,z)$ on the $\sigma$-twisted centralizer $\{t : t\,\delta_A\,\sigma(t)^{-1} = \delta_A\}$ which are Haar for $u \neq 1$ and, when $\gamma_\infty(u,z)$ is a norm, are `Coupled` to $\tau_A(u,z)$ with conjugator $1$, that is the pushforward of $\tau_A'(u,z)$ along the inclusion equals the pushforward of $\tau_A(u,z)$ along $\mathrm{toTensorGL}$ (`hτA'c`). Likewise elements $\delta_F(u,z,v)$ with the corresponding norm-string identity for $v \in S_K$ (`hδF`), and measures $\tau_F'(u,z,v)$ on the twisted centralizer of $\delta_F(u,z,v)$, Haar for $u \neq 1$ and of mass $1$ on the preimage of $\mathrm{semiLocalIntegralSet}$. The quantities $J_A'(u,z)$ are twisted weighted orbital integrals of $\varphi_a \circ \mathrm{archIdentGL}$ at $\delta_A(u,z)$ for $\nu_A'$ and $\tau_A'(u,z)$, with weight $y \mapsto -\log \mathrm{archHeight}_L(\mathrm{archIdentGL}\, y) - \log \mathrm{archHeight}_L(w_{L,\infty}\cdot \mathrm{archIdentGL}\, y)$, whenever $\gamma_\infty(u,z)$ is a norm, and $J_A'(u,z) = 0$ otherwise (`hJA'0`); the $J_F'(u,z,v)$ ($v \in S_K$) are twisted weighted orbital integrals of $\varphi_S(v)$ at $\delta_F(u,z,v)$ for `semiLocalHaar` and the semilocal weight (a sum over the extensions of $v$ to $L$), whenever $\gamma_v(u,z)$ is a norm, and $J_F'(u,z,v) = 0$ otherwise.
--
--   *The remaining finite places.* For $u \neq 1$, $I_T(u,z,v)$ ($v \in T$) is the local orbital integral of $f_T(v)$ at $\gamma_v(u,z)$ for $\tau_F(u,z,v)$, and $I_U(u,z,v)$ ($v \notin S_K \cup T$) is the local orbital integral at $\gamma_v(u,z)$ of the indicator function of $\mathrm{localIntegralSet}$ with value $1$.
--
--   Under these hypotheses, for every $u \in K^\times$ with $u \neq 1$ the following two assertions hold.
--
--   (A) The function $z \mapsto \prod^{\mathrm{f}}_{v \notin S_K \cup T} I_U(u,z,v)$, the `finprod` over all finite places $v$ of the `finprod` over the proposition $v \notin S_K \cup T$ of $I_U(u,z,v)$, is locally constant on $(\mathbb{A}_K)^\times$.
--
--   (B) For every $d \in (\mathbb{A}_K)^\times$ and every monoid homomorphism $\xi$ from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi(z) \in \mathbb{C}$ is continuous, the function
--   $$z \mapsto \xi(z)\Bigl[\Bigl(\prod_{v \in T} I_T(u,zd,v)\Bigr)\Bigl(\prod^{\mathrm{f}}_{v \notin S_K \cup T} I_U(u,zd,v)\Bigr)\Bigl(\bigl(J_A'(u,zd) - [L:K]\,J_A(u,zd)\bigr)\prod_{v \in S_K} I_F(u,zd,v) + I_A(u,zd)\sum_{v \in S_K}\bigl(J_F'(u,zd,v) - [L:K]\,J_F(u,zd,v)\bigr)\prod_{v' \in S_K \setminus \{v\}} I_F(u,zd,v')\Bigr)\Bigr]$$
--   is integrable with respect to $\nu_{Z_K}$, the factor $[L:K]$ being the degree $\operatorname{finrank}_K L$ cast into $\mathbb{C}$, and the inner product over $v' \in S_K \setminus \{v\}$ being taken over `SK.erase v`.
--
--   This is the analytic input for the hyperbolic (weighted) terms in the comparison of trace formulae for cyclic base change of prime degree for $\mathrm{GL}_2$: it records that the product over the places outside $S_K \cup T$ of the unramified orbital integrals is locally constant in the central idele, and that the full window integrand, twisted by a continuous character and translated by $d$, is $\nu_{Z_K}$-integrable, so that the winding integral may be formed and Fubini applied. It is used in the assembly of the hyperbolic intercept and the associated Satake–Laurent expansion in [`AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn.lean

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
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.isLocallyConstant_finprod_unitValue_and_integrable_window_product_of_ne_one_of_isLocalTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ SK, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))

    (fT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfT : ∀ v ∈ T, AutomorphicForm.IsLocalTestFn K v (fT v))

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
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        (u : K) ≠ 1 →
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

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))
    (JA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (JA u z))
    (JF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsWeightedOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (JF u z v))

    (νA' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hνA : νA = AutomorphicForm.archHaarK K) (hνA' : νA' = AutomorphicForm.archHaarL K L)
    (δA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (δA u z) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z)))
    (hτA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τA' u z).IsHaarMeasure)
    (hτA'c : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (δA u z) 1 (τA u z) (τA' u z))
    (δF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ (δF u z v) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v)))
    (hτF' : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → (τF' u z v).IsHaarMeasure)
    (hτF'1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (JA' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ νA'
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
        (δA u z) (τA' u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z))
    (hJA'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) → JA' u z = 0)
    (JF' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF u z v) (τF' u z v) (φS v) (JF' u z v))
    (hJF'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      JF' u z v = 0)

    (IT : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIT : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fT v) (IT u z v))
    (IU : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIU : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∉ SK ∪ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v)
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (IU u z v))
    :
    ∀ (u : Kˣ), (u : K) ≠ 1 →
      IsLocallyConstant (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u z v) ∧
      ∀ (d : (AdeleRing (𝓞 K) K)ˣ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ),
        Continuous (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ =>
          ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ((∏ v ∈ T, IT u (z * d) v) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u (z * d) v) *
          ((JA' u (z * d) - (Module.finrank K L : ℂ) * JA u (z * d)) * ∏ v ∈ SK, IF u (z * d) v +
            IA u (z * d) * ∑ v ∈ SK, (JF' u (z * d) v - (Module.finrank K L : ℂ) * JF u (z * d) v) *
              ∏ v' ∈ SK.erase v, IF u (z * d) v'))) νZK := by sorry
