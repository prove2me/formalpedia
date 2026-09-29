-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal
-- name    : AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a6c0496b-a412-59c6-a809-2b0a744ae87b
-- title:
--   Uniform germ bound for twisted weighted orbital integrals at t=1
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields, $\sigma$ an element of $\mathrm{Gal}(L/K)$ such that every $\tau$ lies in the subgroup of integer powers of $\sigma$, and suppose $\ell = [L:K]$ is prime; let $v$ be a height-one prime of $\mathcal{O}_K$, with completion $K_v$. Let $\varphi$ on $\mathrm{GL}_2(L\otimes_K K_v)$ and $f$ on $\mathrm{GL}_2(K_v)$ be locally constant functions of compact support which satisfy `AreMatchingLocal`: twisted orbital integrals of $\varphi$ against semi-local Haar measure agree with orbital integrals of $f$ against local Haar measure for norm-conjugate regular semisimple pairs with coupled Haar measures on the relevant centralisers, and orbital integrals of $f$ vanish at regular semisimple $\gamma$ admitting no norm. Let $\mu$ be an additive Haar measure on $K_v$ with $\mu(\mathcal{O}_v)=1$. Then there are $\Lambda : K_v^\times \to \mathbb{C}$, a real $C$, and a neighbourhood $U$ of $1$ in $K_v^\times$, such that for all $a,t \in K_v^\times$ with $t \neq 1$ and $t \in U$ both of the following hold. First, for all units $\alpha,\beta$ of $L\otimes_K K_v$ whose twisted norm string $\prod_{i=0}^{\ell-1}\sigma_{\mathrm{GL}}^{i}(\mathrm{diag}(\alpha,\beta))$ (where $\sigma_{\mathrm{GL}}$ acts entrywise through $\sigma\otimes\mathrm{id}$) equals the image of $\mathrm{diag}(a,at)$ under the map $\mathrm{GL}_2(K_v)\to\mathrm{GL}_2(L\otimes_K K_v)$ induced by $x \mapsto 1\otimes x$, for every Haar measure $\tau'$ on the $\sigma$-twisted centraliser $\{x : x\delta\sigma_{\mathrm{GL}}(x)^{-1}=\delta\}$ of $\delta=\mathrm{diag}(\alpha,\beta)$ giving mass $1$ to the subset of elements lying in `semiLocalIntegralSet` (those $g$ with $g$ and $g^{-1}$ having entries in the semi-local integers), and every $J'$ which is a twisted weighted orbital integral of $\varphi$ at $\delta$ against $\tau'$ for the semi-local weight and semi-local Haar measure, one has $$\bigl\| \|1-t\|\,\sqrt{\|a\|/\|at\|}\,J' + 2\ell \cdot H(a,at) - \Lambda(a)\bigr\| \le C\,\|1-t\|\,\bigl(1+|\log\|1-t\||\bigr),$$ where $H(a,b) = -\sqrt{\|a\|/\|b\|}\int_{\|x\|>\|1-ba^{-1}\|} \mathrm{slice}(f)(a,b,x)\,(\log\|x\| - \log\|1-ba^{-1}\|)\,d\mu(x)$ is `halfWeighted` formed from the local Haar measure on $\mathrm{GL}_2(K_v)$ restricted to `localIntegralSet` and from $\mu$, with the absolute value on $K_v$ as norm function. Second, if no such $\alpha,\beta$ exist, then $\|2\ell\cdot H(a,at) - \Lambda(a)\|$ satisfies the same bound.
--
--   This is the local germ estimate at $t=1$ for the normalised twisted weighted orbital integral of $\varphi$ against $2\ell$ times Langlands' half-weight attached to $f$, in the radial direction $\mathrm{diag}(a,at)$ at a finite place: the singular parts cancel and the difference from a function $\Lambda$ of $a$ alone is $O(\|1-t\|(1+|\log\|1-t\||))$, uniformly in $a$ and in the admissible data $(\delta,\tau',J')$. It merges the two cases (diagonal element a twisted norm or not) into a single statement with one $\Lambda$, one constant and one neighbourhood, and is used in the derivation of the limiting identity for weighted orbital integrals in the comparison of twisted and untwisted trace formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal.lean

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

theorem AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal
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
    ∃ (Λ : (v.adicCompletion K)ˣ → ℂ) (C : ℝ), ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ),
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
        (∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
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
          (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) - Λ a‖ ≤
                C * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|)) ∧
        ((¬ ∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) →
          ‖2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) - Λ a‖ ≤
            C * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|)) := by sorry
