-- Prove2me | Theorems.Thm_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
-- name    : AutomorphicForm.twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/71665a3c-6644-5095-96d2-3465a3ca139d
-- title:
--   Invariance of twisted window values under (u,z)↦(u⁻¹,zι u)
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ a finite Galois extension, $\sigma : L \simeq_{\mathrm{alg}[K]} L$ is an automorphism such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$ (hypothesis `hgen`), and $[L:K] =$ `Module.finrank K L` is prime (`hprime`). A Haar measure $\nu_{Z,K}$ on the idele unit group $(\mathbb{A}_K)^\times$ is fixed, together with two disjoint finite sets $S_K$ and $T$ of finite places of $K$ (`hTS : Disjoint T SK`). Write $\iota : K^\times \to (\mathbb{A}_K)^\times$ for the map induced by $K \to \mathbb{A}_K$, and, for $u \in K^\times$ and $z \in (\mathbb{A}_K)^\times$, write
--   $$\gamma(u,z) := \mathrm{centralScalar}(z)\cdot \mathrm{diagUnits2}(\iota u)\,1 \in \mathrm{GL}_2(\mathbb{A}_K),$$
--   that is, the scalar matrix $z$ times $\mathrm{diag}(\iota u, 1)$; its archimedean component is $\gamma_\infty(u,z) =$ `AdelicLevel.glArch` $\gamma(u,z)$ and its component at a finite place $v$ is $\gamma_v(u,z) =$ `AdelicLevel.finComponent` $v$ (`AdelicLevel.glFin` $\gamma(u,z)$).
--
--   The hypotheses fall into the following groups.
--
--   *Test data and matching* (`faK`, `hfaK`, `fSK`, `hfSK`, `φa`, `hφa`, `φS`, `hφS`, `hmatchA`, `hmatchS`): $f_{a,K}$ is an archimedean test factor for $K$ (a compactly supported function on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ given by a smooth function of the matrix entries read in the mixed space), $f_{S_K,v}$ is a locally constant compactly supported function on $\mathrm{GL}_2(K_v)$ for each $v \in S_K$, $\varphi_a$ is an archimedean test factor for $L$, and $\varphi_{S,v}$ is a locally constant compactly supported function on $\mathrm{GL}_2(L \otimes_K K_v)$ for $v \in S_K$. The matching hypotheses `hmatchA` and `hmatchS` assert `AreMatchingArch` for the pair $(\varphi_a, f_{a,K})$ and `AreMatchingLocal` for each pair $(\varphi_{S,v}, f_{S_K,v})$, $v \in S_K$: for $\delta$ with `normString` regular semisimple and $\gamma$ regular semisimple conjugated to it by a norm conjugator $y$, all Haar measures on the ordinary and $\sigma$-twisted centralisers that are `Coupled` through $y$ give equal twisted orbital integral of $\varphi$ and orbital integral of $f$, and every orbital integral of $f$ at a regular semisimple $\gamma$ admitting no norm vanishes.
--
--   *Auxiliary places* (`fT`, `hfT`, `hmatchT`, `hunit`): for $v \in T$ the function $f_{T,v}$ on $\mathrm{GL}_2(K_v)$ is locally constant with compact support and admits some locally constant compactly supported semilocal partner $\varphi_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$ matching it in the sense of `AreMatchingLocal`; at every $v$ outside $S_K \cup T$, the indicator of `semiLocalIntegralSet` matches the indicator of `localIntegralSet`.
--
--   *Global factorisation of the test function* (`f`, `ff`, `hf`): $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ and $f_f$ on $\mathrm{GL}_2(\mathbb{A}_{K,\mathrm{fin}})$ satisfy `IsUnitFactorization` for the finite set $S_K \cup T$ with archimedean factor $f_{a,K}$ and local family $v \mapsto f_{T,v}$ for $v \in T$, $v \mapsto f_{S_K,v}$ otherwise; that is, the factors are test functions of the respective kinds, $f_f(h)$ equals the product of the local factors over $S_K \cup T$ whenever all components of $h$ outside $S_K \cup T$ lie in `localIntegralSet`, $f_f(h) = 0$ when some component outside $S_K \cup T$ fails to lie there, and $f(g) = f_{a,K}(\mathrm{glArch}\,g)\cdot f_f(\mathrm{glFin}\,g)$.
--
--   *Measure normalisations and product formulae* (`νA`, `cG`, `hG`, `cτK`, `hcτK`, `τG`, `hτG`, `hτGc`, `τA`, `hτA`, `τF`, `hτF`, `hτF1`, `cT`, `hcT`, `hT`, summarised here): $\nu_A$ is a measure on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and $c_G$ a real constant such that for every finite set $S$ and every function on $\mathrm{GL}_2(\mathbb{A}_K)$ which, under the stated measurability assumptions, factorises as an archimedean factor times the product of local factors over $S$ and vanishes when some component outside $S$ leaves `localIntegralSet`, the integral against `adelicGLHaar` equals $c_G$ times the archimedean integral times the product of the local integrals against `localHaar`. Further, $c_{\tau,K} > 0$ and, for each $(u,z)$, $\tau_G(u,z)$ is a measure on the centraliser of $\gamma(u,z)$ in $\mathrm{GL}_2(\mathbb{A}_K)$, Haar for $u \neq 1$, whose integrals are $c_{\tau,K}$ times the corresponding integrals over the diagonal torus against $\nu_{Z,K} \times \nu_{Z,K}$; $\tau_A(u,z)$ and $\tau_F(u,z,v)$ are measures on the centralisers of $\gamma_\infty(u,z)$ and of $\gamma_v(u,z)$, Haar for $u \neq 1$, the latter normalised so that the preimage of `localIntegralSet` has measure $1$; and $c_T > 0$ together with `hT` provides the analogous factorisation of integrals over the centraliser of $\gamma(u,z)$ into an archimedean integral against $\tau_A(u,z)$ times local integrals against $\tau_F(u,z,v)$, with constant $c_T$.
--
--   *Untwisted orbital data* (`IA`, `hIA`, `IF`, `hIF`, `JA`, `hJA`, `JF`, `hJF`, `IT`, `hIT`, `IU`, `hIU`): for $u \neq 1$, $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at $\gamma_\infty(u,z)$ against $\nu_A$ and $\tau_A(u,z)$; $I_F(u,z,v)$ is a local orbital integral of $f_{S_K,v}$ at $\gamma_v(u,z)$ against $\tau_F(u,z,v)$ for $v \in S_K$; $J_A(u,z)$ is a weighted orbital integral of $f_{a,K}$ at $\gamma_\infty(u,z)$ for the weight $y \mapsto -\log H_K(y) - \log H_K(\mathrm{glArch}(\mathrm{adelicWeyl})\cdot y)$, where $H_K$ is [`AutomorphicForm.WindowedSiegel.archHeight`](def/AutomorphicForm_WindowedSiegelSet.html#L48) for $K$; $J_F(u,z,v)$ is a weighted local orbital integral of $f_{S_K,v}$ at $\gamma_v(u,z)$ for $v \in S_K$; $I_T(u,z,v)$ is an orbital integral of $f_{T,v}$ for $v \in T$; and $I_U(u,z,v)$ is an orbital integral of the indicator of `localIntegralSet` for $v \notin S_K \cup T$.
--
--   *Twisted side* (`νA'`, `hνA`, `hνA'`, `δA`, `hδA`, `τA'`, `hτA'`, `hτA'c`, `δF`, `hδF`, `τF'`, `hτF'`, `hτF'1`, `JA'`, `hJA'`, `hJA'0`, `JF'`, `hJF'`, `hJF'0`): $\nu_{A}'$ is a measure on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, and the archimedean measures are pinned down by $\nu_A =$ `archHaarK` $K$ and $\nu_A' =$ `archHaarL` $K\,L$. For each $(u,z)$, $\delta_A(u,z) \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ is such that, when $u \neq 1$ and $\gamma_\infty(u,z)$ admits some norm in the sense of `IsNormOf`, its `normString` (the product of the first $[L:K]$ iterates of $\sigma$ applied to it) equals `toTensorGL` $\gamma_\infty(u,z)$; $\tau_A'(u,z)$ is a Haar measure on the $\sigma$-twisted centraliser of $\delta_A(u,z)$ which, under the same norm hypothesis, is `Coupled` to $\tau_A(u,z)$ with conjugator $1$. Likewise $\delta_F(u,z,v) \in \mathrm{GL}_2(L \otimes_K K_v)$ has `normString` equal to `toTensorGL` $\gamma_v(u,z)$ whenever $u \neq 1$, $v \in S_K$ and $\gamma_v(u,z)$ admits a norm, and $\tau_F'(u,z,v)$ is a Haar measure on the twisted centraliser of $\delta_F(u,z,v)$ giving mass $1$ to the preimage of `semiLocalIntegralSet`. Finally, for $u \neq 1$: $J_A'(u,z)$ is a twisted weighted orbital integral of $\varphi_a \circ$ `archIdentGL` at $\delta_A(u,z)$ against $\nu_A'$ and $\tau_A'(u,z)$ for the weight $y \mapsto -\log H_L(\mathrm{archIdentGL}\,y) - \log H_L(\mathrm{glArch}(\mathrm{adelicWeyl}_L)\cdot \mathrm{archIdentGL}\,y)$ whenever $\gamma_\infty(u,z)$ admits a norm, and $J_A'(u,z) = 0$ when it does not; and for $v \in S_K$, $J_F'(u,z,v)$ is a twisted weighted orbital integral of $\varphi_{S,v}$ at $\delta_F(u,z,v)$ against $\tau_F'(u,z,v)$ (with the semilocal weight) whenever $\gamma_v(u,z)$ admits a norm, and $J_F'(u,z,v) = 0$ when it does not.
--
--   The conclusion is the following symmetry of the twisted window values. For every $u \in K^\times$ and every $z \in (\mathbb{A}_K)^\times$ with $u \neq 1$ in $K$, both of the following hold.
--
--   First, if there exists $\delta$ with [`AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ`](def/AutomorphicForm_TwistedOrbital.html#L217) $\gamma_\infty(u,z)\ \delta$, then
--   $$J_A'\bigl(u^{-1},\, z\cdot \iota u\bigr) = J_A'(u,z).$$
--
--   Second, for every $v \in S_K$: if there exists $\delta$ with [`AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ`](def/AutomorphicForm_TwistedOrbital.html#L217) $\gamma_v(u,z)\ \delta$, then
--   $$J_F'\bigl(u^{-1},\, z\cdot \iota u\bigr)(v) = J_F'(u,z)(v).$$
--
--   In both conjuncts the norm hypothesis is imposed on the original pair $(u,z)$, and the asserted equality compares the value at $(u^{-1}, z\cdot\iota u)$ with the value at $(u,z)$.
--
--   This is the twisted half of the symmetry, under $(u,z) \mapsto (u^{-1}, z\,\iota u)$, of the family of weighted orbital integrals attached to the split regular classes $\mathrm{diag}(\iota u,1)$ twisted by a central idele, as it arises in the comparison of weighted trace formulae for cyclic base change for $\mathrm{GL}(2)$; the symmetry reflects conjugation of $\gamma(u,z)$ by the Weyl element. It is used by [`AutomorphicForm.window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime`](thm.html#AutomorphicForm.window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime), which assembles the untwisted and twisted window values of the same family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.lean

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

theorem AutomorphicForm.twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
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
      ((∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
        JA' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = JA' u z) ∧
      (∀ v ∈ SK,
        (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
          JF' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = JF' u z v) := by sorry
