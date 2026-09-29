-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
-- name    : AutomorphicForm.exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/889a7037-6f1a-53a9-bc35-afd1749c850e
-- title:
--   Iwasawa unfolding of J'+cI' at a diagonal twisted element
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ finite Galois, and let $\sigma$ be an automorphism of $L$ over $K$ such that every $K$-automorphism of $L$ is an integer power of $\sigma$ (so $L/K$ is cyclic with generator $\sigma$). Let $v$ be a nonzero prime of $\mathcal O_K$, write $E=L\otimes_K K_v$ for the semi-local algebra at $v$, equipped with a Borel measurable structure and an additive Haar measure $\nu$, and give $\mathrm{GL}_2(E)$ the Borel $\sigma$-algebra of its topology. Let $\varphi:\mathrm{GL}_2(E)\to\mathbb C$ be locally constant with compact support. Then there is a real $\kappa>0$, independent of all data below, with the following property. Let $\alpha,\beta\in E^\times$ and $a,b\in K_v^\times$ with $a\neq b$, and put $\delta=\mathrm{diag}(\alpha,\beta)$; assume the twisted norm string $\prod_{i<[L:K]}\sigma_{\mathrm{GL}}^{i}(\delta)$, formed from the map $\sigma_{\mathrm{GL}}$ induced on $\mathrm{GL}_2(E)$ by $\sigma\otimes\mathrm{id}$, equals the image of $\mathrm{diag}(a,b)$ under the base-change embedding $\mathrm{GL}_2(K_v)\to\mathrm{GL}_2(E)$. Let $\tau'$ be a Haar measure on the $\sigma$-twisted centraliser of $\delta$ in $\mathrm{GL}_2(E)$ (Borel $\sigma$-algebra) giving mass $1$ to the set of its points lying in the semi-local integral set $\mathrm{GL}_2(\mathcal O_L\otimes\mathcal O_v)$. Let $\beta_s:E\times E\to\mathbb R$ be measurable and nonnegative and be a section normalisation for $\tau'$, in the sense that $\int \beta_s(t_{00}p_1,t_{11}p_2)\,d\tau'(t)=1$ for every pair $p=(p_1,p_2)$ of units of $E$. Finally let $c\in\mathbb R$ and $J',I'\in\mathbb C$ be, respectively, a value of the twisted weighted orbital integral of $\varphi$ at $(\delta,\tau')$ with respect to the semi-local Haar measure on $\mathrm{GL}_2(E)$ and the weight $\mathrm{semiLocalWeight}$ (the finite sum of local weights over the extensions of $v$ to $L$), and a value of the corresponding twisted orbital integral. Set, for $p=(p_1,p_2)$ with $p_1,p_2$ both units, $$F_c(p)=\|N_{E/K_v}(p_1p_2)\|^{-1}\beta_s(p)\int_E\Big(\int_{\mathrm{GL}_2(\mathcal O_L\otimes\mathcal O_v)}\varphi\big(k^{-1}\,\mathrm{diag}(P,Q)\,n(\sigma_E\xi-QP^{-1}\xi)\,\sigma_{\mathrm{GL}}(k)\big)\,dk\Big)\big(W(n(\xi))+c\big)\,d\nu(\xi),$$ and $F_c(p)=0$ otherwise, where $\sigma_E=\sigma\otimes\mathrm{id}$ on $E$, $P=\alpha\,\sigma_E(p_1)p_1^{-1}$, $Q=\beta\,\sigma_E(p_2)p_2^{-1}$, $n(x)$ is the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $W$ is the above weight. The assertion is that $F_c$ is integrable for $\nu\otimes\nu$ and that $J'+cI'=\kappa\int_{E\times E}F_c\,d(\nu\otimes\nu)$, with the same $\kappa$ for all $c$ and all admissible data.
--
--   This is the Iwasawa-coordinate unfolding, at a diagonal element $\delta$ of $\mathrm{GL}_2(E)$ whose twisted norm is a regular split diagonal element of $\mathrm{GL}_2(K_v)$, of the twisted weighted and twisted orbital integrals occurring in the local comparison for cyclic base change of $\mathrm{GL}(2)$; the decomposition $x=\mathrm{diag}(p)\,n(\xi)\,k$ turns both values into integrals over pairs of units against a torus section $\beta_s$, with one Haar normalisation constant $\kappa$ serving both. It feeds the estimate [`AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_mul_log_mul_twistedOrbital_sub_le_of_normString_diagUnits2_eq`](thm.html#AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_mul_log_mul_twistedOrbital_sub_le_of_normString_diagUnits2_eq), where $\kappa$ cancels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b : (v.adicCompletion K)ˣ), a ≠ b →
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) →
        ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
          τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
        ∀ βs : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ, Measurable βs → (∀ p, 0 ≤ βs p) →
          (∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
            @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
              (fun t => βs ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1,
                (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1) →
        ∀ c : ℝ, ∀ J' I' : ℂ,
          AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
          AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ I' →
          Integrable (fun p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) =>
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0)) (ν.prod ν) ∧
          J' + (c : ℂ) * I' = (κ : ℂ) * ∫ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0) ∂(ν.prod ν) := by sorry
