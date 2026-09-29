-- Prove2me | Theorems.Thm_AutomorphicForm_exists_hasCompactSupport_forall_norm_sub_one_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_inv_ratio_mul_sqrtRatio_mul_of_areMatchingLocal
-- name    : AutomorphicForm.exists_hasCompactSupport_forall_norm_sub_one_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_inv_ratio_mul_sqrtRatio_mul_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/d4d02e7d-b585-5ed0-9c43-38ab834c0348
-- title:
--   Local window functions for the finite places of S_K
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois, let $S_K$ be a finite set of finite places of $K$ (height-one primes of $\mathcal{O}_K$), and write $K_v$ for the completion `v.adicCompletion K`. For $u \in K^\times$ and $z \in (\mathbb{A}_K)^\times$ put
--   $$\gamma(u,z,v) \;=\; \mathtt{finComponent}_v\bigl(\mathtt{glFin}\bigl(\mathtt{centralScalar}(z)\cdot \mathrm{diagUnits2}(u_{\mathbb{A}},1)\bigr)\bigr) \in \mathrm{GL}_2(K_v),$$
--   where $u_{\mathbb{A}}$ is the image of $u$ in $(\mathbb{A}_K)^\times$; thus $\gamma(u,z,v)$ is the $v$-component of the diagonal adelic matrix $z\cdot\mathrm{diag}(u,1)$, and by [`AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2`](thm.html#AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2) its matrix is $\mathrm{diag}(z_v u_v, z_v)$.
--
--   The data are: a family $f_{S}$ of functions $\mathrm{GL}_2(K_v) \to \mathbb{C}$, one for each finite place, with `hfSK` asserting that for $v \in S_K$ the function $f_S(v)$ is locally constant and compactly supported; a family $\tau_F(u,z,v)$ of Borel measures on the centraliser of $\gamma(u,z,v)$ in $\mathrm{GL}_2(K_v)$, which by `hτF` and `hτF1` is, whenever the image of $u$ in $K$ is $\ne 1$, a Haar measure of total mass $1$ on the preimage of [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) (the set of elements of $\mathrm{GL}_2(K_v)$ whose matrix and inverse matrix both have entries in $\mathcal{O}_{K_v}$); an automorphism $\sigma$ of $L/K$ with `hgen` asserting that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$, and `hprime` asserting that $\ell := [L:K] = \operatorname{finrank}_K L$ is prime; a family $\varphi_S$ of functions $\mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ which by `hφS` is locally constant and compactly supported for $v \in S_K$, and which by `hmatchS` matches $f_S(v)$ at each $v \in S_K$ in the sense of [`AutomorphicForm.AreMatchingLocal`](def/AutomorphicForm_TwistedOrbital.html#L386) for $\sigma$: with respect to the semi-local Haar measure on $\mathrm{GL}_2(L\otimes_K K_v)$ and the local Haar measure on $\mathrm{GL}_2(K_v)$, twisted orbital integrals of $\varphi_S(v)$ at $\delta$ agree with orbital integrals of $f_S(v)$ at $\gamma$ whenever $\gamma$ and the norm string of $\delta$ are regular semisimple, $y$ is a norm conjugator, and the Haar measures on the centraliser and on the twisted centraliser are coupled, while orbital integrals of $f_S(v)$ vanish at regular semisimple $\gamma$ admitting no norm.
--
--   Further data: complex numbers $J_F(u,z,v)$ which by `hJF`, for $u \ne 1$ in $K$ and $v \in S_K$, are weighted orbital integrals of $f_S(v)$ at $\gamma(u,z,v)$ against $\tau_F(u,z,v)$, i.e. $J_F(u,z,v) = \int \!f_S(v)(x^{-1}\gamma(u,z,v)x)\,\mathrm{weight}(x)\,s(x)\,d\mu$ for the local Haar measure $\mu$ on $\mathrm{GL}_2(K_v)$, the local weight `LocalWeight.weight` and some section function for $\tau_F(u,z,v)$; elements $\delta_F(u,z,v) \in \mathrm{GL}_2(L\otimes_K K_v)$ which by `hδF`, for $u \ne 1$ and $v \in S_K$, satisfy $\mathtt{normString}_\sigma(\delta_F(u,z,v)) = \mathtt{toTensorGL}(\gamma(u,z,v))$ — the norm string being the product $\prod_{i<\ell} \sigma^i(\delta)$ — provided $\gamma(u,z,v)$ admits some norm at all; Borel measures $\tau_F'(u,z,v)$ on the $\sigma$-twisted centraliser $\{t : t\,\delta_F(u,z,v)\,\sigma(t)^{-1} = \delta_F(u,z,v)\}$, which by `hτF'` and `hτF'1` are, for $u \ne 1$, Haar measures of mass $1$ on the preimage of [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136); and complex numbers $J_F'(u,z,v)$ which by `hJF'`, for $u \ne 1$ and $v \in S_K$ and provided $\gamma(u,z,v)$ admits a norm, are twisted weighted orbital integrals $\int \!\varphi_S(v)(x^{-1}\delta_F(u,z,v)\sigma(x))\,\mathtt{semiLocalWeight}(x)\,s(x)$ against the semi-local Haar measure, with `semiLocalWeight` the sum of the local weights over the extensions of $v$ to $L$, while by `hJF'0` $J_F'(u,z,v) = 0$ when $\gamma(u,z,v)$ admits no norm.
--
--   The conclusion asserts the existence of a family $\Psi_f$ assigning to every finite place $v$ of $K$ a function $\Psi_f(v) : K_v^\times \times K_v^\times \to \mathbb{C}$ with the following five properties.
--
--   First, for every $v \in S_K$ the function $\Psi_f(v)$ has compact support. Second, for every $v \in S_K$ and every $p \in K_v^\times \times K_v^\times$ with second coordinate $\ne 1$ there is a neighbourhood $U$ of $p$ on which $\Psi_f(v)$ is constant, equal to $\Psi_f(v)(p)$. Third, for every $v \in S_K$ there are a neighbourhood $U$ of $1$ in $K_v^\times$ and a real $\rho > 0$ such that for all $a, a', t, t' \in K_v^\times$ with $t \in U$, $\|a' - a\| \le \rho\|a\|$ and $\|t' - t\| \le \rho\|1 - t\|$ one has $\Psi_f(v)(a',t') = \Psi_f(v)(a,t)$. Fourth, for every $v \in S_K$ there is a real constant $C$ with
--   $$\|\Psi_f(v)(a,t) - \Psi_f(v)(a,1)\| \;\le\; C\,\|1-t\|\,\bigl(1 + |\log\|1-t\||\bigr)$$
--   for all $a, t \in K_v^\times$.
--
--   Fifth, for every $u \in K^\times$ whose image in $K$ is $\ne 1$, every $z_S \in (\mathbb{A}_K)^\times$ and every $v \in S_K$, writing $u_v$ for the $v$-component of the finite-adele part of the image of $u$ in $\mathbb{A}_K$, and writing $a = (z_S u)_v$ and $t = (u_v)^{-1}$ for the images in $K_v^\times$ of $z_S u_{\mathbb{A}}$ and of $u_{\mathbb{A}}^{-1}$ under the place map [`AutomorphicForm.adelePlaceAlgHom K v`](def/AutomorphicForm_BaseChangePlaces.html#L20),
--   $$\|u_v - 1\|\,\bigl(J_F'(u,z_S,v) - \ell\, J_F(u,z_S,v)\bigr) \;=\; \|u_v - 1\|\,\bigl(\mathrm{ratio}(a, a t)\cdot \mathrm{sqrtRatio}(a, a t)\bigr)^{-1}\,\Psi_f(v)(a, t),$$
--   where the two real factors are formed with the norm of $K_v$, namely $\mathrm{ratio}(a,b) = \|1 - b a^{-1}\|$ and $\mathrm{sqrtRatio}(a,b) = \sqrt{\|a\|/\|b\|}$, their product is inverted after coercion to $\mathbb{C}$, and $\|u_v - 1\|$ is likewise coerced from $\mathbb{R}$ to $\mathbb{C}$. The common factor $\|u_v-1\|$ on both sides means that the identity carries no content at places where $u_v = 1$, and that no invertibility of $1 - t$ need be assumed.
--
--   This is the local, finite-place half of the comparison between twisted and plain weighted orbital integrals for cyclic base change of prime degree on $\mathrm{GL}_2$: the discrepancy $J' - \ell J$ at each $v \in S_K$ is expressed through a single family of window functions $\Psi_f(v)$ on $K_v^\times \times K_v^\times$ carrying compact support, local constancy away from $t = 1$, invariance on multiplicative cells near $t=1$, and a logarithmic germ bound at $t = 1$. It is used in the global summation step [`AutomorphicForm.exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted`](thm.html#AutomorphicForm.exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted), where these four properties are exactly what the window is required to satisfy.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_hasCompactSupport_forall_norm_sub_one_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_inv_ratio_mul_sqrtRatio_mul_of_areMatchingLocal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
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

theorem AutomorphicForm.exists_hasCompactSupport_forall_norm_sub_one_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_inv_ratio_mul_sqrtRatio_mul_of_areMatchingLocal
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    [IsGalois K L]
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ SK, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))
    (hmatchS : ∀ v ∈ SK, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fSK v))
    (JF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsWeightedOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (JF u z v))
    (δF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ (δF u z v) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v)))
    (hτF' : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → (τF' u z v).IsHaarMeasure)
    (hτF'1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (JF' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF u z v) (τF' u z v) (φS v) (JF' u z v))
    (hJF'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      JF' u z v = 0) :
    ∃ Ψf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      (∀ v ∈ SK, HasCompactSupport (Ψf v)) ∧
      (∀ v ∈ SK, ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Ψf v q = Ψf v p) ∧
      (∀ v ∈ SK, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : v.adicCompletion K) - (a : v.adicCompletion K)‖ ≤ ρ * ‖(a : v.adicCompletion K)‖ →
        ‖(t' : v.adicCompletion K) - (t : v.adicCompletion K)‖ ≤
            ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ →
          Ψf v (a', t') = Ψf v (a, t)) ∧
      (∀ v ∈ SK, ∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
      ‖Ψf v (a, t) - Ψf v (a, 1)‖ ≤ C * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ *
        (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|)) ∧
      ∀ u : Kˣ, (u : K) ≠ 1 → ∀ (zS : (AdeleRing (𝓞 K) K)ˣ), ∀ v ∈ SK,
        (((‖((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖) : ℝ) : ℂ) * (JF' u zS v - (Module.finrank K L : ℂ) * JF u zS v) =
          (((‖((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖) : ℝ) : ℂ) * ((((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) * (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) *
                        AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) * (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) : ℝ)) : ℂ))⁻¹ * Ψf v ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))), (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) := by sorry
