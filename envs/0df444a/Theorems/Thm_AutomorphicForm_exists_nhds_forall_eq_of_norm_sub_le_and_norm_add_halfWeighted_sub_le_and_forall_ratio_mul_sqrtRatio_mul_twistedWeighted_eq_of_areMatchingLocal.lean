-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_eq_of_norm_sub_le_and_norm_add_halfWeighted_sub_le_and_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_areMatchingLocal
-- name    : AutomorphicForm.exists_nhds_forall_eq_of_norm_sub_le_and_norm_add_halfWeighted_sub_le_and_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/36de1de2-a77a-5a6e-87d5-99ae3f9d8a94
-- title:
--   Twisted weighted orbital germ near t=1 at a finite place
-- statement:
--   Let $L/K$ be an extension of number fields which is finite and Galois, let $\sigma$ be an automorphism of $L$ over $K$ whose integral powers exhaust $\mathrm{Gal}(L/K)$, and assume $[L:K]$ is prime. Let $v$ be a nonzero prime of $\mathcal{O}_K$, write $K_v$ for the completion and $\mathcal{O}_v$ for its valuation ring. Let $\varphi : \mathrm{GL}_2(L\otimes_K K_v)\to\mathbb{C}$ and $f : \mathrm{GL}_2(K_v)\to\mathbb{C}$ be locally constant with compact support, and assume $\varphi$ and $f$ are matching in the sense of `AreMatchingLocal` for $\sigma$: twisted orbital integrals of $\varphi$ against the semi-local Haar measure agree with the corresponding orbital integrals of $f$ against the local Haar measure at coupled regular semisimple data, and orbital integrals of $f$ vanish at regular semisimple $\gamma$ admitting no norm. Let $\mu$ be an additive Haar measure on $K_v$ with $\mu(\mathcal{O}_v)=1$. Then, with $\mathrm{GL}_2(K_v)$ carrying its Borel structure, there are a function $\Psi : K_v^\times\times K_v^\times\to\mathbb{C}$, a neighbourhood $U$ of $1$ in $K_v^\times$ and a real $\rho>0$ such that: (i) $\Psi(a',t')=\Psi(a,t)$ whenever $t\in U$, $\|a'-a\|\le\rho\|a\|$ and $\|t'-t\|\le\rho\|1-t\|$; (ii) there is a constant $C$ with $$\bigl\|\bigl(\Psi(a,t)+2[L:K]\,H(a,at)\bigr)-\bigl(\Psi(a,1)+2[L:K]\,H(a,a\cdot 1)\bigr)\bigr\|\le C\,\|1-t\|\,\bigl(1+|\log\|1-t\||\bigr)$$ for all $a,t\in K_v^\times$, where $H(a,b)=-\sqrt{\|a\|/\|b\|}\int_{\|x\|>\|1-ba^{-1}\|}\bigl(\int f(\mathrm{arg}\,k\,a\,b\,x)\,\mathrm{d}k\bigr)\bigl(\log\|x\|-\log\|1-ba^{-1}\|\bigr)\,\mathrm{d}\mu(x)$ is `halfWeighted` formed from the local Haar measure on $\mathrm{GL}_2(K_v)$ restricted to the integral set $\{g : g,g^{-1}\in M_2(\mathcal{O}_v)\}$, from $\mu$, and from the norm on $K_v$; and (iii) for all $a$ and all $t\in U$ with $t\neq 1$: whenever $\alpha,\beta\in (L\otimes_K K_v)^\times$ satisfy $\mathrm{normString}$ of $\mathrm{diag}(\alpha,\beta)$, the product $\prod_{i<[L:K]}\sigma^i\bigl(\mathrm{diag}(\alpha,\beta)\bigr)$, equal to the image of $\mathrm{diag}(a,at)$ under $\mathrm{GL}_2(K_v)\to\mathrm{GL}_2(L\otimes_K K_v)$, then for every Haar measure $\tau'$ on the $\sigma$-twisted centraliser $\{x : x\delta\sigma(x)^{-1}=\delta\}$ of $\delta=\mathrm{diag}(\alpha,\beta)$ giving mass $1$ to the points lying in the semi-local integral set, and every $J'$ which is a twisted weighted orbital integral of $\varphi$ at $\delta$ against $\tau'$ (with the semi-local weight and semi-local Haar measure), one has $\|1-t\|\sqrt{\|a\|/\|at\|}\cdot J'=\Psi(a,t)$; and if no such pair $(\alpha,\beta)$ exists, then $\Psi(a,t)=0$.
--
--   This is the finite-place germ comparison underlying the local theory of twisted weighted orbital integrals in base change for $\mathrm{GL}(2)$ over a cyclic extension of prime degree: the normalised twisted weighted orbital integral of $\varphi$ along the diagonal family $\gamma_t=\mathrm{diag}(a,at)$ is represented by a single function $\Psi$, constant on the cells $\|a'-a\|\le\rho\|a\|$, $\|t'-t\|\le\rho\|1-t\|$, and its logarithmic singularity at $t=1$ cancels against $2[L:K]$ times the half-weighted integral of $f$ up to $O(\|1-t\|\log\|1-t\|)$. It feeds the subsequent statement in which the twisted normalisation is compared with the weighted integral of $f$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_eq_of_norm_sub_le_and_norm_add_halfWeighted_sub_le_and_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_areMatchingLocal.lean

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

theorem AutomorphicForm.exists_nhds_forall_eq_of_norm_sub_le_and_norm_add_halfWeighted_sub_le_and_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_areMatchingLocal
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
    ∃ Ψ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      (∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : v.adicCompletion K) - (a : v.adicCompletion K)‖ ≤ ρ * ‖(a : v.adicCompletion K)‖ →
        ‖(t' : v.adicCompletion K) - (t : v.adicCompletion K)‖ ≤
            ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ →
          Ψ (a', t') = Ψ (a, t)) ∧
      (∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
        ‖(Ψ (a, t) + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : v.adicCompletion K => ‖x‖) f a (a * t)) -
          (Ψ (a, 1) + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : v.adicCompletion K => ‖x‖) f a (a * 1))‖ ≤
          C * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ *
          (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|)) ∧
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
          ((∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * J' = Ψ (a, t)) ∧
          ((¬ ∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) → Ψ (a, t) = 0)) := by sorry
