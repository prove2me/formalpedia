-- Prove2me | Theorems.Thm_AutomorphicForm_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
-- name    : AutomorphicForm.window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/7b490613-3b01-5ac8-aec4-a7955d34c70d
-- title:
--   Invariance of window values under (u,z)↦(u⁻¹,zu)
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ a finite Galois extension, $\sigma \in \mathrm{Gal}(L/K)$ is an element whose integral powers exhaust the Galois group (hypothesis `hgen`), and the degree $[L:K] =$ `Module.finrank K L` is prime (`hprime`). A Haar measure $\nu_{Z_K}$ on the idele class group $(\mathbb{A}_K)^\times$ is fixed, and $S_K$, $T$ are finite sets of finite places of $K$ with $T$ disjoint from $S_K$ (`hTS`). All the groups of adelic, local and semi-local $2\times 2$ matrices carry their Borel structures.
--
--   The family of elements under consideration is
--   $$\gamma(u,z) \;=\; \mathrm{centralScalar}(z)\cdot \mathrm{diagUnits2}(u,1),$$
--   the product of the scalar matrix with entry $z \in (\mathbb{A}_K)^\times$ and the diagonal matrix $\mathrm{diag}(u,1)$, where $u \in K^\times$ is pushed into $(\mathbb{A}_K)^\times$ along `algebraMap`; `glArch` and `finComponent ∘ glFin` denote its archimedean component and its component at a finite place $v$.
--
--   *Test data and matching.* The function $f_{a,K}$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ is an archimedean test factor (`hfaK`): it is given by a smooth function of the matrix entries viewed in the mixed space of $K$, and has compact support. For $v \in S_K$ the function $f_{S_K,v}$ on $\mathrm{GL}_2(K_v)$ is locally constant with compact support (`hfSK`), and likewise $\varphi_a$ is an archimedean test factor for $L$ (`hφa`) and $\varphi_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$ is locally constant with compact support for $v \in S_K$ (`hφS`). The matching hypotheses `hmatchA` and `hmatchS` assert `AreMatchingArch` for the pair $(\varphi_a, f_{a,K})$ and `AreMatchingLocal` for each pair $(\varphi_{S,v}, f_{S_K,v})$, $v \in S_K$: for regular semisimple $\delta$ (with regular semisimple norm string) and $\gamma$ linked by a norm conjugator, coupled Haar measures on the twisted centraliser and on the centraliser force the twisted orbital integral of the $L$-side function to equal the orbital integral of the $K$-side function, and the orbital integrals of the $K$-side function vanish at regular semisimple $\gamma$ admitting no norm.
--
--   *Data at the auxiliary places $T$ and outside.* For $v \in T$ the function $f_{T,v}$ is locally constant with compact support (`hfT`) and admits a semi-local partner: some locally constant, compactly supported $\varphi_v$ on $\mathrm{GL}_2(L\otimes_K K_v)$ with `AreMatchingLocal` for $(\varphi_v, f_{T,v})$ (`hmatchT`). Outside $S_K \cup T$ the hypothesis `hunit` requires the indicator of `semiLocalIntegralSet` and the indicator of `localIntegralSet` to match in the same sense.
--
--   *Global factorisation.* The pair $(f, f_f)$ satisfies `IsUnitFactorization` at level $S_K \cup T$ with archimedean factor $f_{a,K}$ and local factors $f_{T,v}$ for $v \in T$, $f_{S_K,v}$ otherwise (`hf`): $f_f$ is locally constant with compact support, $f_f(h)$ is the product of the local factors over $S_K\cup T$ when all components of $h$ outside $S_K \cup T$ lie in the local integral sets, $f_f(h) = 0$ when some such component does not, and $f(g) = f_{a,K}(g_\infty)\, f_f(g_{\mathrm{fin}})$.
--
--   *Measure factorisations.* With $\nu_A$ a measure on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and a real constant $c_G$, the hypothesis `hG` states: for every finite set $S$ of finite places and every triple $(f, f_a, f_S)$ with $f_a$ almost everywhere strongly measurable for $\nu_A$ and each $f_S(v)$, $v \in S$, almost everywhere strongly measurable for `localHaar`, if $f(g)$ equals $f_a(g_\infty)\prod_{v \in S} f_S(v)(g_v)$ whenever all components of $g$ outside $S$ lie in the local integral sets and $f(g) = 0$ whenever some component outside $S$ does not, then $\int f \,d(\mathrm{adelicGLHaar})$ equals $c_G\,(\int f_a \,d\nu_A)\prod_{v\in S}\int f_S(v)\,d(\mathrm{localHaar})$.
--
--   The tori are pinned as follows. For each $u, z$ there is a measure $\tau_G(u,z)$ on the centraliser of $\gamma(u,z)$ in $\mathrm{GL}_2(\mathbb{A}_K)$, Haar whenever $u \neq 1$ (`hτG`), and the hypothesis `hτGc` computes its integrals: for $u \neq 1$ and any $g$, $\int_{Z(\gamma(u,z))} g(t)\, d\tau_G(u,z) = c_{\tau K}\int\!\!\int g(\mathrm{diag}(p_1,p_2))\, d(\nu_{Z_K}\times\nu_{Z_K})$, with $c_{\tau K} > 0$ (`hcτK`). Similarly $\tau_A(u,z)$ is a measure on the centraliser of the archimedean component of $\gamma(u,z)$, Haar for $u \neq 1$ (`hτA`), and $\tau_F(u,z,v)$ is a measure on the local centraliser of the component of $\gamma(u,z)$ at $v$, Haar for $u \neq 1$ (`hτF`) and of total mass $1$ on the preimage of `localIntegralSet` (`hτF1`). With a constant $c_T > 0$ (`hcT`), the hypothesis `hT` factorises $\tau_G$-integrals: for $u \neq 1$, any $z$, any finite $S$ and any $(W, W_a, W_S)$ satisfying the corresponding measurability conditions, the product formula on the centraliser off $S$ and vanishing when some component off $S$ fails to be integral, one has $\int W \,d\tau_G(u,z) = c_T\,(\int W_a\, d\tau_A(u,z))\prod_{v\in S}\int W_S(v)\, d\tau_F(u,z,v)$.
--
--   *The window values.* For $u \neq 1$: $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at the archimedean component of $\gamma(u,z)$ against $\nu_A$ and $\tau_A(u,z)$ (`hIA`), that is, $I_A = \int f_{a,K}(x^{-1}\gamma_\infty x)\,w(x)\,d\nu_A$ for some non-negative measurable compactly supported $w$ whose $\tau_A$-integral along the centraliser coset through $x$ is $1$ whenever the integrand does not vanish; $I_F(u,z,v)$ is the analogous local orbital integral of $f_{S_K,v}$ for $v \in S_K$ (`hIF`); $J_A(u,z)$ is the weighted orbital integral of $f_{a,K}$ with weight
--   $$y \mapsto -\log \mathrm{archHeight}_K(y) - \log \mathrm{archHeight}_K\bigl(\mathrm{adelicWeyl}_\infty \cdot y\bigr)$$
--   (`hJA`), and $J_F(u,z,v)$ is the weighted local orbital integral of $f_{S_K,v}$ with weight `LocalWeight.weight` for $v \in S_K$ (`hJF`).
--
--   *Twisted side.* The measures are normalised by $\nu_A = \mathrm{archHaarK}$ and $\nu_A' = \mathrm{archHaarL}$ (`hνA`, `hνA'`). For $u \neq 1$, whenever the archimedean component of $\gamma(u,z)$ is a norm, $\delta_A(u,z)$ is chosen so that its norm string $\delta\,\sigma(\delta)\cdots\sigma^{[L:K]-1}(\delta)$ equals the image of that component under `toTensorGL` (`hδA`); $\tau_A'(u,z)$ is a Haar measure on the $\sigma$-twisted centraliser of $\delta_A(u,z)$ (`hτA'`) coupled to $\tau_A(u,z)$ with conjugator $1$ (`hτA'c`), meaning the pushforwards of $\tau_A'$ under the inclusion and of $\tau_A$ under `toTensorGL` agree. The same applies at $v \in S_K$ with $\delta_F(u,z,v)$ (`hδF`) and Haar measures $\tau_F'(u,z,v)$ (`hτF'`) of total mass $1$ on the preimage of `semiLocalIntegralSet` (`hτF'1`). Then $J_A'(u,z)$ is a twisted weighted orbital integral of $\varphi_a \circ \mathrm{archIdentGL}$ at $\delta_A(u,z)$ with the $L$-side archimedean height weight, under the norm guard (`hJA'`), and $J_A'(u,z) = 0$ when the guard fails (`hJA'0`); correspondingly $J_F'(u,z,v)$ for $v \in S_K$ is a twisted weighted orbital integral of $\varphi_{S,v}$ at $\delta_F(u,z,v)$ with weight `semiLocalWeight` under the local guard (`hJF'`), and vanishes when that guard fails (`hJF'0`).
--
--   Finally, $I_T(u,z,v)$ is the local orbital integral of $f_{T,v}$ for $v \in T$ (`hIT`), and $I_U(u,z,v)$ is the local orbital integral of the indicator of `localIntegralSet` for $v \notin S_K \cup T$ (`hIU`).
--
--   **Conclusion.** For every $u \in K^\times$ and every $z \in (\mathbb{A}_K)^\times$ with $u \neq 1$ in $K$, writing $z u$ for the product of $z$ with the image of $u$ in $(\mathbb{A}_K)^\times$, the following hold:
--
--   1. $I_A(u^{-1}, zu) = I_A(u,z)$;
--
--   2. $J_A(u^{-1}, zu) = J_A(u,z)$;
--
--   3. if the archimedean component of $\gamma(u,z)$ admits a $\sigma$-norm, i.e. there exists $\delta$ with `IsNormOf` for it, then $J_A'(u^{-1}, zu) = J_A'(u,z)$;
--
--   4. for every $v \in S_K$: $I_F(u^{-1}, zu, v) = I_F(u,z,v)$, $J_F(u^{-1}, zu, v) = J_F(u,z,v)$, and, if the component of $\gamma(u,z)$ at $v$ admits a $\sigma$-norm, $J_F'(u^{-1}, zu, v) = J_F'(u,z,v)$;
--
--   5. for every $v \in T$: $I_T(u^{-1}, zu, v) = I_T(u,z,v)$;
--
--   6. for every finite place $v$ with $v \notin S_K$ and $v \notin T$: $I_U(u^{-1}, zu, v) = I_U(u,z,v)$.
--
--   In the two conditional clauses the norm guard is imposed on the parameters $(u,z)$, not on $(u^{-1}, zu)$.
--
--   This is the symmetry statement for the hyperbolic contributions in the comparison of the base-change trace formulae for $\mathrm{GL}_2$ over $K$ and over the cyclic extension $L$: the parametrisation of split regular elements by $(u,z) \mapsto \mathrm{diag}(zu,z)$ is two-to-one, the two parameters $(u,z)$ and $(u^{-1},zu)$ giving conjugate elements, and the assertion is that all the plain, weighted and twisted weighted window values are constant on these pairs. It is obtained from the untwisted and twisted forms of the same symmetry, [`AutomorphicForm.ground_window_values_inv_mul_unitsMap_eq_of_ne_one`](thm.html#AutomorphicForm.ground_window_values_inv_mul_unitsMap_eq_of_ne_one) and [`AutomorphicForm.twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime`](thm.html#AutomorphicForm.twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime), and is used in the assembly of the hyperbolic term as a sum over oriented parameters in [`AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.lean

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

theorem AutomorphicForm.window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
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
    (hmatchA : AutomorphicForm.AreMatchingArch K L σ φa faK)
    (hmatchS : ∀ v ∈ SK, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fSK v))

    (fT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfT : ∀ v ∈ T, AutomorphicForm.IsLocalTestFn K v (fT v))
    (hmatchT : ∀ v ∈ T, ∃ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv (fT v))
    (hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T →
      AutomorphicForm.AreMatchingLocal K L v σ
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))

    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (SK ∪ T) f faK ff (fun v => if v ∈ T then fT v else fSK v))

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
    ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 →
      IA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = IA u z ∧
      JA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = JA u z ∧
      ((∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
        JA' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = JA' u z) ∧
      (∀ v ∈ SK,
        IF u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = IF u z v ∧
        JF u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = JF u z v ∧
        ((∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
          JF' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = JF' u z v)) ∧
      (∀ v ∈ T, IT u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = IT u z v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → IU u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = IU u z v) := by sorry
