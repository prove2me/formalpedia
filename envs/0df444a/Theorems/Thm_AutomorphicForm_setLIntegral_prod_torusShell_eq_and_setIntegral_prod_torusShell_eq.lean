-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq
-- name    : AutomorphicForm.setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9e411e03-e9aa-5f37-bd60-9b25ad83c0fb
-- title:
--   Exact value of the torus-shell integral over Ω_L×Ω_K
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha<\beta$ be reals, let $\nu_{ZL}$ and $\nu_K$ be Haar measures on the idele groups $\mathbb{A}_L^\times$ and $\mathbb{A}_K^\times$ (each carrying a Borel measurable structure), and let $\Omega_L\subseteq\mathbb{A}_L^\times$, $\Omega_K\subseteq\mathbb{A}_K^\times$ be fundamental domains for the action of the ranges of the principal-idele maps $L^\times\to\mathbb{A}_L^\times$, $K^\times\to\mathbb{A}_K^\times$. Let $\theta\colon\mathbb{A}_K^\times\to\mathbb{A}_L^\times$ be a continuous group homomorphism with $\|\theta a\|_L=\|a\|_K^{[L:K]}$, the norms being the values of the distributive Haar character; let $y\in\mathrm{GL}_2(\mathbb{A}_L)$ and $R\in\mathbb{R}$. Write $g(z,a)=(z\cdot I_2)\,\mathrm{diag}(\theta a,1)\,y$, let $H$ denote `adelicHeight` for $L$ (the product of the archimedean and finite local heights), let $w$ be the image in $\mathrm{GL}_2(\mathbb{A}_L)$ of the antidiagonal matrix $!![0,1;1,0]\in\mathrm{GL}_2(L)$, and let $T(z,a)\in\mathbb{C}$ be the product of the indicator of $\{\|\det\|_L\in[\alpha,\beta]\}$ at $g(z,a)$ with $1-\bigl(\mathbf 1[e^R<H]-\mathbf 1[e^R<H(w\,\cdot)]\bigr)$ at $g(z,a)$. Put $\kappa=V_LV_K\log(\beta/\alpha)/(2[L:K])$ with $V_L=\nu_{ZL}(\Omega_L\cap\{\|z\|_L\in[1,e]\})$, $V_K=\nu_K(\Omega_K\cap\{\|a\|_K\in[1,e]\})$ (real parts of the extended-real values), and $A=2R-\log H(y)-\log H(wy)$. Then the lower Lebesgue integral of $\|T\|_e$ over $\Omega_L\times\Omega_K$ against $\nu_{ZL}\otimes\nu_K$ equals $\mathrm{ofReal}(\kappa|A|)$; and if $H(y)H(wy)\le e^{2R}$ then $T$ is integrable on $\Omega_L\times\Omega_K$ with integral the complex number $\kappa A$.
--
--   This is the explicit volume computation for the slab-and-bracket integrand of $\mathrm{GL}_2$ written in idelic coordinates $(z,a)$ on a product of fundamental domains, giving both the finiteness statement (as a lower Lebesgue integral of the norm) and the exact value of the Bochner integral. It is used by [`AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq`](thm.html#AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ)
    (hθn : ∀ a, NumberField.TateGlobal.ideleNorm L (θ a) = NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L)
    (y : AdelicGL2 (𝓞 L) L) (R : ℝ) :
    (∫⁻ p in ΩL ×ˢ ΩK, ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))‖ₑ ∂(νZL.prod νK) =
      ENNReal.ofReal (((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L)) * |(2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))|)) ∧
    (NumberField.AdelicHeight.adelicHeight L y *
        NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y) ≤ Real.exp (2 * R) →
      IntegrableOn (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))) (ΩL ×ˢ ΩK) (νZL.prod νK) ∧
      ∫ p in ΩL ×ˢ ΩK, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y))) ∂(νZL.prod νK) =
        ((((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L)) * (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) : ℝ) : ℂ)) := by sorry
