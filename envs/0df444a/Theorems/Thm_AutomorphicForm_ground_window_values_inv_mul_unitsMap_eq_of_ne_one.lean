-- Prove2me | Theorems.Thm_AutomorphicForm_ground_window_values_inv_mul_unitsMap_eq_of_ne_one
-- name    : AutomorphicForm.ground_window_values_inv_mul_unitsMap_eq_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/470b2692-232c-5a73-ae53-7a0e5f9084ac
-- title:
--   Invariance of ground window values under (u,z)↦(u⁻¹,zι u)
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite Galois, and $\sigma$ is a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$ (hypothesis `hgen`), while `hprime` asserts that $[L:K]$ is prime. The unit group $(\mathbb{A}_K)^\times$ of the adele ring carries a measurable structure which is the Borel structure of its topology, and $\nu_{Z_K}$ is a Haar measure on it. Two finite sets $S_K, T$ of finite places of $K$ are given, with $T$ disjoint from $S_K$ (`hTS`). For $u \in K^\times$ and $z \in (\mathbb{A}_K)^\times$ write $\iota u$ for the image of $u$ under the map induced by $K \to \mathbb{A}_K$, and
--   $$\gamma_{u,z} \;=\; \mathrm{centralScalar}(z)\cdot \mathrm{diagUnits2}(\iota u)\,1 \;=\; \mathrm{diag}(z\,\iota u,\;z) \in \mathrm{GL}_2(\mathbb{A}_K),$$
--   whose archimedean and $v$-adic components are taken by `AdelicLevel.glArch` and `AdelicLevel.finComponent ∘ AdelicLevel.glFin` respectively.
--
--   **Test data and matching.** $f_{a,K}$ is an archimedean test factor on $\mathrm{GL}_2(K_\infty)$ (a compactly supported function given by a smooth function of the matrix entries read in the mixed space of $K$), and for $v \in S_K$ the function $f_{S_K}(v)$ on $\mathrm{GL}_2(K_v)$ is locally constant with compact support. On the $L$-side, $\varphi_a$ is an archimedean test factor on $\mathrm{GL}_2(L_\infty)$ and, for $v \in S_K$, $\varphi_S(v)$ is a locally constant compactly supported function on $\mathrm{GL}_2(L\otimes_K K_v)$. The hypotheses `hmatchA` and `hmatchS` assert the $\sigma$-matching `AreMatchingArch`/`AreMatchingLocal` of these pairs: for regular semisimple norms, coupled Haar measures on the ordinary and the $\sigma$-twisted centralisers force the twisted orbital integral of the $L$-side function to equal the ordinary orbital integral of the $K$-side function, and the ordinary orbital integral vanishes at regular semisimple elements admitting no norm. Further, $f_T(v)$ is a local test function for $v \in T$ (`hfT`), each $f_T(v)$ admits a semi-local test function matching it (`hmatchT`), and outside $S_K \cup T$ the indicator of `semiLocalIntegralSet` matches the indicator of `localIntegralSet` (`hunit`). The pair $(f, f_f)$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ and on $\mathrm{GL}_2(\mathbb{A}_{K,\mathrm{fin}})$ is a unit factorisation relative to $S_K\cup T$ with archimedean factor $f_{a,K}$ and local factors $f_T(v)$ for $v \in T$, $f_{S_K}(v)$ otherwise (`hf`): $f_f$ is locally constant with compact support, equals the product of the local factors over $S_K\cup T$ at arguments whose components outside $S_K \cup T$ are integral, vanishes when some component outside $S_K\cup T$ is not integral, and $f(g) = f_{a,K}(g_\infty)\,f_f(g_{\mathrm{fin}})$.
--
--   **Measures and product formulae.** $\nu_A$ is a measure on $\mathrm{GL}_2(K_\infty)$ for the Borel structure, and the constant $c_G$ together with `hG` expresses the global Haar integral as a product: for every finite set $S$ of finite places and all $F$, $f_a$, $f_S$ which are suitably strongly measurable and satisfy the factorisation $F(g) = f_a(g_\infty)\prod_{v\in S} f_S(v)(g_v)$ at arguments integral outside $S$ and vanish when some component outside $S$ is not integral, one has $\int F \,d(\mathrm{adelicGLHaar}) = c_G\,(\int f_a\,d\nu_A)\prod_{v\in S}\int f_S(v)\,d(\mathrm{localHaar}\,K\,v)$. The family $\tau_G(u,z)$ consists of measures on the centraliser of $\gamma_{u,z}$ in $\mathrm{GL}_2(\mathbb{A}_K)$, Haar for $u \ne 1$ (`hτG`), and `hτGc` identifies integration over that centraliser with $c_{\tau_K} > 0$ times integration of $p \mapsto g(\mathrm{diagUnits2}\,p_1\,p_2)$ against $\nu_{Z_K}\times\nu_{Z_K}$. Similarly $\tau_A(u,z)$ are measures on the centraliser of the archimedean component of $\gamma_{u,z}$, Haar for $u\ne 1$, and $\tau_F(u,z,v)$ are measures on the local centraliser of its $v$-component, Haar for $u \ne 1$ and of total mass $1$ on the preimage of `localIntegralSet` (`hτF1`). The constant $c_T > 0$ and `hT` give the corresponding product formula for centraliser integrals: under the analogous measurability, factorisation and vanishing hypotheses, $\int W\,d\tau_G(u,z) = c_T\,(\int W_a\,d\tau_A(u,z))\prod_{v\in S}\int W_S(v)\,d\tau_F(u,z,v)$ whenever $(u:K)\ne 1$.
--
--   **Window values.** For $(u:K) \ne 1$: $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at the archimedean component of $\gamma_{u,z}$ against $\nu_A$ and $\tau_A(u,z)$ (`hIA`); $I_F(u,z,v)$, for $v \in S_K$, is a local orbital integral of $f_{S_K}(v)$ at the $v$-component against $\tau_F(u,z,v)$ (`hIF`); $J_A(u,z)$ is a weighted orbital integral of $f_{a,K}$ for the weight $y \mapsto -\log \mathrm{archHeight}_K(y) - \log \mathrm{archHeight}_K(w_\infty y)$, with $w_\infty$ the archimedean component of the adelic Weyl element (`hJA`); and $J_F(u,z,v)$, for $v \in S_K$, is a weighted local orbital integral of $f_{S_K}(v)$ for the local weight (`hJF`). On the $L$-side, $\nu_{A}'$ is a measure on $\mathrm{GL}_2(L\otimes_K K_\infty)$, and `hνA`, `hνA'` fix $\nu_A$ and $\nu_A'$ to be the Haar measures `archHaarK` and `archHaarL`. The elements $\delta_A(u,z)$ satisfy, when a norm of the archimedean component of $\gamma_{u,z}$ exists, that their norm string equals the image of that component under `toTensorGL` (`hδA`); $\tau_A'(u,z)$ are Haar measures on the $\sigma$-twisted centraliser of $\delta_A(u,z)$ (`hτA'`) coupled to $\tau_A(u,z)$ through the conjugator $1$ (`hτA'c`). Likewise $\delta_F(u,z,v)$ for $v \in S_K$ (`hδF`), with $\tau_F'(u,z,v)$ Haar of mass $1$ on the preimage of `semiLocalIntegralSet` (`hτF'`, `hτF'1`). The quantities $J_A'(u,z)$ are twisted weighted orbital integrals of $\varphi_a \circ \mathrm{archIdentGL}$ at $\delta_A(u,z)$ for the weight built from $\mathrm{archHeight}_L$ and the Weyl element of $L$ (`hJA'`), and vanish when no norm exists (`hJA'0`); the $J_F'(u,z,v)$ are twisted weighted local orbital integrals of $\varphi_S(v)$ at $\delta_F(u,z,v)$ for $v \in S_K$ (`hJF'`), vanishing when no norm exists (`hJF'0`). Finally $I_T(u,z,v)$, for $v \in T$, is a local orbital integral of $f_T(v)$ (`hIT`), and $I_U(u,z,v)$, for $v \notin S_K\cup T$, a local orbital integral of the indicator of `localIntegralSet` (`hIU`), both at the $v$-component of $\gamma_{u,z}$ against $\tau_F(u,z,v)$.
--
--   **Conclusion.** For every $u \in K^\times$ and every $z \in (\mathbb{A}_K)^\times$ with $(u:K) \ne 1$, all five of the following hold:
--   $$I_A(u^{-1},\,z\,\iota u) = I_A(u,z), \qquad J_A(u^{-1},\,z\,\iota u) = J_A(u,z);$$
--   for every $v \in S_K$, both $I_F(u^{-1}, z\,\iota u, v) = I_F(u,z,v)$ and $J_F(u^{-1}, z\,\iota u, v) = J_F(u,z,v)$; for every $v \in T$, $I_T(u^{-1}, z\,\iota u, v) = I_T(u,z,v)$; and for every finite place $v$ with $v \notin S_K$ and $v \notin T$, $I_U(u^{-1}, z\,\iota u, v) = I_U(u,z,v)$. Thus only the $K$-side plain and weighted window values occur in the conclusion, and each is unchanged by the substitution $(u,z) \mapsto (u^{-1}, z\,\iota u)$.
--
--   The substitution $(u,z)\mapsto(u^{-1},z\,\iota u)$ sends $\mathrm{diag}(z\iota u, z)$ to the Weyl conjugate $\mathrm{diag}(z, z\iota u)$, so this is the statement that the plain and weighted orbital-integral window values attached to the split torus family over $K$ are symmetric functions of the two diagonal entries. It is the ground-field half of the symmetry used in the comparison of the $K$-side and $L$-side sides of the twisted trace identity, and is cited by [`AutomorphicForm.window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime`](thm.html#AutomorphicForm.window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ground_window_values_inv_mul_unitsMap_eq_of_ne_one.lean

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

theorem AutomorphicForm.ground_window_values_inv_mul_unitsMap_eq_of_ne_one
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
      (∀ v ∈ SK,
        IF u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = IF u z v ∧
        JF u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = JF u z v) ∧
      (∀ v ∈ T, IT u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = IT u z v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → IU u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = IU u z v) := by sorry
