-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
-- name    : AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/7edae354-9144-58cd-aed4-846395b84e4d
-- title:
--   Twisted minus untwisted weighted orbital germ at t=1
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite and Galois, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of the group lies in $\langle \sigma \rangle$, and assume $[L:K]$ is prime. Let $v$ be a nonzero prime of $\mathcal O_K$, let $\varphi$ on $\mathrm{GL}_2(L \otimes_K K_v)$ and $f$ on $\mathrm{GL}_2(K_v)$ be complex-valued, locally constant and compactly supported, matching in the sense of `AreMatchingLocal` (twisted orbital integrals of $\varphi$ against the semi-local Haar measure agree with orbital integrals of $f$ against the local Haar measure at coupled regular semisimple data, and orbital integrals of $f$ vanish at regular semisimple $\gamma$ that are not norms), and let $\mu$ be an additive Haar measure on $K_v$ with $\mu(\mathcal O_v) = 1$. Then there are a function $\Lambda_1 : K_v^\times \to \mathbb C$, a constant $C_1 \in \mathbb R$ and a neighbourhood $U$ of $1$ in $K_v^\times$ such that for all $a, t \in K_v^\times$ with $t \neq 1$, $t \in U$, and all units $\alpha, \beta$ of $L \otimes_K K_v$ whose twisted norm string $\prod_{i<[L:K]} \sigma^i(\mathrm{diag}(\alpha,\beta))$ equals the image of $\mathrm{diag}(a, at)$ under $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$, the following holds for every Haar measure $\tau'$ on the $\sigma$-twisted centraliser $\{x : x\,\delta\,\sigma(x)^{-1} = \delta\}$ of $\delta = \mathrm{diag}(\alpha,\beta)$, carrying its Borel structure, which gives mass $1$ to the part of the semi-local integral set, and for every $J' \in \mathbb C$ realised as a twisted weighted orbital integral $\int \varphi(x^{-1}\delta\,\sigma(x))\, w(x)\, s(x)$ of $\varphi$ at $\delta$ with respect to $\tau'$ (semi-local Haar measure, semi-local weight $w$, some twisted section function $s$): $$\bigl\| \|1 - t a a^{-1}\|\,(\|a\|/\|at\|)^{1/2} J' + 2[L:K]\,\mathrm{halfWeighted}(a, at) - \Lambda_1(a) \bigr\| \le C_1 \|1 - t\|\,\bigl(1 + |\log \|1-t\||\bigr),$$ where the first factor is `ratio` $= \|1 - (at)a^{-1}\|$ times `sqrtRatio`, and $\mathrm{halfWeighted}$ is $-(\|a\|/\|at\|)^{1/2}$ times the integral over $\{x : \|1-(at)a^{-1}\| < \|x\|\}$ of the slice of $f$ at $(a, at)$, taken against the local Haar measure on $\mathrm{GL}_2(K_v)$ restricted to the integral set, weighted by $\log\|x\| - \log\|1-(at)a^{-1}\|$ and integrated against $\mu$.
--
--   This is the local germ estimate comparing the twisted weighted orbital integral of $\varphi$ with $[L:K]$ times the logarithmic weighted term of a matching $f$ as the regular diagonal element $\mathrm{diag}(a,at)$ degenerates to a central one, with error of order $\|1-t\|(1+|\log\|1-t\||)$; it is the matching-function form of the comparison appearing in Langlands' treatment of base change for $\mathrm{GL}(2)$. It is used by [`AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal`](thm.html#AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean

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

theorem AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1) :
    letI := AutomorphicForm.localGLBorel K v
    ∃ (Λ₁ : (v.adicCompletion K)ˣ → ℂ) (C₁ : ℝ), ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ),
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
        ∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ‖((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J' + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) - Λ₁ a‖ ≤
                C₁ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|) := by sorry
