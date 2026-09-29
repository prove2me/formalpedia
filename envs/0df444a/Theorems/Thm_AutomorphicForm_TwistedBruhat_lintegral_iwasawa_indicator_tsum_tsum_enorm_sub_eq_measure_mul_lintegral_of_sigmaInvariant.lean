-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant
-- name    : AutomorphicForm.TwistedBruhat.lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/a9e970ff-ab5c-5935-9fcf-3555c1707a95
-- title:
--   Removing the central variable from the unipotent-type Iwasawa lower integral
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha\le\beta$ be reals, let $\nu_{Z_L}$ be a Haar measure on the idele group $(\mathbb A_L)^\times$ (Borel measurable structure) and let $\Omega_L$ be a fundamental domain, with respect to $\nu_{Z_L}$, for the subgroup of principal ideles, i.e. the range of $L^\times\to(\mathbb A_L)^\times$. Let $D$ be an [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A_L$, continuous and compatible with $\mathrm{algebraMap}$ on $L$, and let $\sigma\in\mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integral powers of $\sigma$. Let $\xi_L$ be a homomorphism from the full idele group to $\mathbb C^\times$ whose associated complex function is continuous, which is trivial on principal ideles and satisfies $\xi_L(\mathrm{unitsAct}\,D\,\sigma\,z_0)=\xi_L(z_0)$ for all $z_0$. Let $\varphi:\mathrm{GL}_2(\mathbb A_L)\to\mathbb C$ be continuous with compact support, $R$ a real, $X$ a set of adeles, and $\Omega_1,\Omega_2$ sets of ideles with $\Omega_1$ a fundamental domain for the principal ideles with respect to [`NumberField.Idele.idelicHaar`](def/NumberField_IdeleProductMeasure.html#L391). For $g\in\mathrm{GL}_2(\mathbb A_L)$ write $F(g)$ for the lower integral over $z\in\Omega_L$ against $\nu_{Z_L}$ of $\|\xi_L(z)\|_e$ times the double sum over $s\in L^\times$ and over $a\in L^\times$ with $N_{L/K}(a)=1$ of the extended norm of the difference of two terms: first, the finite sum over those $\delta\in\mathrm{GL}_2(L)$ belonging to `TwistedBruhat.normUnipotentSet K L σ hgen` (those whose $\sigma$-conjugacy class has norm class the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ of unipotent type) and satisfying $\delta_{10}=0$, $\delta_{11}=s$, $\delta_{00}=sa$, of $\varphi\bigl(g^{-1}\,\iota(\delta)\,\mathrm{act}_D(\sigma)(z\cdot g)\bigr)$, where $\iota$ is the entrywise map $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb A_L)$, $z\cdot g$ means the scalar matrix $z$ times $g$ and $\mathrm{act}_D(\sigma)$ acts entrywise; second, the indicator of $\{h:\exp R<\mathrm{adelicHeight}(h)\}$ at $z\cdot g$ times the constant term of the same sum taken over the $\delta$ with only the three entry conditions, namely its integral over unipotent translates $n(q)(z\cdot g)$ with $q$ distributed by the adelic Haar measure conditioned on the adelic box. The assertion is that the iterated lower integral over $x\in X$ (adelic Haar), $u\in\Omega_1$, $t\in\Omega_2$ (idelic Haar) and $k$ in the adelic maximal compact subgroup (its Haar measure) of the indicator of $\{g:\|\det g\|\in[\alpha,\beta]\}$ applied to $F$ at $g=n(x)\,z(u)\,\mathrm{diag}(t,1)\,k$, weighted by $\|t\|^{-1}$, equals the idelic Haar volume of $\Omega_1\cap\{u:\|u\|^2\in[\alpha,\beta]\}$ times the same iterated lower integral over $x,t,k$ only, of $F\bigl(n(x)\,\mathrm{diag}(t,1)\,k\bigr)\,\|t\|^{-1}$; here $\|\cdot\|$ is the idele norm given by the module of the distributive Haar character.
--
--   This is the central-variable reduction for the Iwasawa-coordinate form of the fibrewise absolute integrand attached to the unipotent-type part of the $\sigma$-twisted cusp kernel minus its truncated constant term: integration over the central factor $u$ decouples and contributes only the volume of the norm shell in the fundamental domain $\Omega_1$. It is used in [`AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2`](thm.html#AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2), where the remaining $x$, $t$ and $k$ integrals are evaluated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.TwistedBruhat.lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L)) :
    (∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * g))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * g)‖ₑ ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) =
      NumberField.Idele.idelicHaar L (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) *
      (∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
            (∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) := by sorry
