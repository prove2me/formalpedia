-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal
-- name    : AutomorphicForm.exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/c3da8ca3-5b84-5fd2-b434-88bccb6335e3
-- title:
--   Uniform cells for twisted lifts and normalised weighted orbital values
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and assume $[L:K]$ is prime. Let $v$ be a nonzero prime of $\mathcal{O}_K$, write $K_v$ for the $v$-adic completion, let $\varphi : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ be locally constant with compact support, let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be locally constant with compact support, and assume $\varphi$ and $f$ match locally at $v$ in the sense of [`AutomorphicForm.AreMatchingLocal`](def/AutomorphicForm_TwistedOrbital.html#L386), i.e. `AreMatchingOn` for $\sigma$ with respect to the semi-local and local Haar measures. The assertion is that there are a neighbourhood $U$ of $1$ in $K_v^\times$ and a real $\rho > 0$ such that for all units $a, a', t, t'$ of $K_v$ with $t \in U$, $\|a' - a\| \le \rho\|a\|$, $\|t' - t\| \le \rho\|1 - t\|$, $t \ne 1$ and $t' \ne 1$, both of the following hold. First, there exist units $\alpha, \beta$ of $L \otimes_K K_v$ whose $\sigma$-norm string $\prod_{i<[L:K]} \sigma^i(\mathrm{diag}(\alpha,\beta))$ (formed via `sigmaGL`) equals the image of $\mathrm{diag}(a, at)$ under the map $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$ induced by $x \mapsto 1 \otimes x$ if and only if the same holds with $(a, at)$ replaced by $(a', a't')$. Second, for all $\alpha, \beta$ with $\sigma$-norm string equal to the image of $\mathrm{diag}(a, at)$, every Haar measure $\tau'$ for the Borel structure on the $\sigma$-twisted centraliser of $\mathrm{diag}(\alpha,\beta)$ giving mass $1$ to the set of its elements lying in [`AutomorphicForm.semiLocalIntegralSet`](def/AutomorphicForm_TwistedOrbital.html#L136), every $J' \in \mathbb{C}$ that is a twisted weighted orbital integral of $\varphi$ at $\mathrm{diag}(\alpha,\beta)$ with respect to $\tau'$, and all corresponding data $\alpha', \beta', \tau'', J''$ at $\mathrm{diag}(a', a't')$, one has $$\|1 - (at)a^{-1}\|\,(\|a\|/\|at\|)^{1/2}\,J' = \|1 - (a't')a'^{-1}\|\,(\|a'\|/\|a't'\|)^{1/2}\,J'',$$ i.e. the normalising factor is the product of `ratio` and `sqrtRatio` for the norm $\|\cdot\|$ on $K_v$, evaluated at the pairs $(a, at)$ and $(a', a't')$.
--
--   This is the local germ statement near $t = 1$ used in the comparison of twisted weighted orbital integrals for the cyclic extension $L/K$ of prime degree: on a single cell the existence of a diagonal element whose $\sigma$-norm string represents a given regular diagonal conjugacy class, and the normalised twisted weighted value, are both constant. It packages the two halves into one neighbourhood and one radius, and is used by the subsequent statement combining these uniformities with the half-weighted local estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal.lean

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

theorem AutomorphicForm.exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)  :
    ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ * ‖(a : (v.adicCompletion K))‖ →
        ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ →
        t ≠ 1 → t' ≠ 1 →
        ((∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) ↔
          (∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' (a' * t')))) ∧
        (∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ∀ α' β' : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α' β') =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' (a' * t')) →
            ∀ (τ'' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α' β'))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β'))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β')) τ'' →
              τ'' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J'' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α' β') τ'' φ J'' →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J' = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') : ℝ) : ℂ) * J'') := by sorry
