-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_exists_entire_mul_eulerProduct_eq_and_ne_zero_and_norm_le_mul_pow_archParam_weight_mul_norm_of_isInducedSection_principalLevel
-- name    : AutomorphicForm.exists_forall_exists_entire_mul_eulerProduct_eq_and_ne_zero_and_norm_le_mul_pow_archParam_weight_mul_norm_of_isInducedSection_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/0ecc93b9-61c5-5a99-840f-67d755812e2c
-- title:
--   Uniform polynomial bound for partial L-factors on the unitary axis
-- statement:
--   Let $K$ be a number field, let $S_K$ be a finite set of finite places of $K$, let $N$ be an ideal of $\mathcal O_K$ all of whose prime divisors lie in $S_K$, and let $S$ be a finite set of finite places with $S_K\subseteq S$. Write $\alpha$ for the character $(\mathbb A_K)^\times\to\mathbb R^\times$ obtained from the module (`distribHaarChar`) of the adele ring. The assertion is that there are a real $C>0$ and a natural number $A$, depending only on these data, such that the following holds whenever $\alpha$ takes only positive values, $\mu,\nu:(\mathbb A_K)^\times\to\mathbb C^\times$ are continuous characters which are unitary ($|\mu(x)|=|\nu(x)|=1$ for all $x$) and trivial on the principal ideles $K^\times$, the families $\tau^\mu,\tau^\nu:\mathrm{InfinitePlace}(K)\to\mathbb R$ and $m^\mu,m^\nu:\mathrm{InfinitePlace}(K)\to\mathbb Z$ describe the archimedean components of $\mu$ and $\nu$, in the sense that at each infinite place $v$ the character $x\mapsto\mu(\iota_v(x))$ on $(K_v)^\times$, where $\iota_v$ is the central embedding of $(K_v)^\times$ into the idele units, equals $\|\iota_v(x)\|^{\,i\tau^\mu_v}$ for $x$ mapping to a positive real under the extension embedding, and equals $x^{m^\mu_v}$ for $x$ of absolute value $1$ (and similarly for $\nu$), $s_0\in\mathbb C$, and $\varphi:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ is a nonzero function satisfying $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for all $g$ and all $b$ in the adelic Borel subgroup, with $\eta_1=\mu\cdot\alpha^{s_0+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s_0+1/2)}$, and which is right invariant under the intersection of the principal level subgroup of level $N$ with the kernel of the archimedean projection, and $(\varpi_v)_v$ is any family of elements of $(K_v)^\times$ of valuation $-1$ under `Multiplicative.ofAdd`: then there exist entire functions $G,p:\mathbb C\to\mathbb C$ with $$G(s)\prod_{v\notin S}\bigl(1-\chi_v(\varpi_v)\,(\#(\mathcal O_K/v))^{-(2s+1)}\bigr)=p(s)\qquad(\operatorname{Re}s>1),$$ where $\chi=\mu\nu^{-1}$ and $\chi_v$ is its local component at $v$, and such that for every real $t$ one has $G(it)\ne 0$ and $$\|p(it)\|\le C\Bigl(1+\sum_{v\mid\infty}\bigl(|t+\tau^\mu_v|+|t-\tau^\nu_v|+|m^\mu_v|+|m^\nu_v|\bigr)\Bigr)^{A}\,\|G(it)\|.$$
--
--   The product over $v\notin S$ is the reciprocal of the partial Hecke $L$-function $L^S(2s+1,\mu\nu^{-1})$, which is the normalising factor appearing in the constant term and Whittaker expansion of the $\mathrm{GL}_2$ Eisenstein series attached to the induced section $\varphi$; the statement packages its meromorphic continuation as a quotient $p/G$ of entire functions together with a lower bound for $|G|$, uniform over all pairs of unitary idele class characters admitting a nonzero section of level $N$, and polynomial in the archimedean parameters and weights. It is used in the estimate of the axis continuation of the Eisenstein constant term on compact flat sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_exists_entire_mul_eulerProduct_eq_and_ne_zero_and_norm_le_mul_pow_archParam_weight_mul_norm_of_isInducedSection_principalLevel.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_exists_entire_mul_eulerProduct_eq_and_ne_zero_and_norm_le_mul_pow_archParam_weight_mul_norm_of_isInducedSection_principalLevel
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : SK ⊆ S)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (s₀ : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s₀) (etaSnd ν αm hαm s₀) φ)
      (_hφ0 : φ ≠ 0)
      (_hφlev : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g)
      (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)),
    ∃ (G p : ℂ → ℂ), Differentiable ℂ G ∧ Differentiable ℂ p ∧
      (∀ s : ℂ, 1 < s.re →
        G s * (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
            (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) = p s) ∧
      ∀ t : ℝ, G ((t : ℂ) * Complex.I) ≠ 0 ∧
        ‖p ((t : ℂ) * Complex.I)‖ ≤
          C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
            ‖G ((t : ℂ) * Complex.I)‖ := by sorry
