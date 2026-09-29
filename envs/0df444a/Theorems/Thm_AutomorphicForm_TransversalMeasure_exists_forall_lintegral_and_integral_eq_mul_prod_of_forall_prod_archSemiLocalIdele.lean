-- Prove2me | Theorems.Thm_AutomorphicForm_TransversalMeasure_exists_forall_lintegral_and_integral_eq_mul_prod_of_forall_prod_archSemiLocalIdele
-- name    : AutomorphicForm.TransversalMeasure.exists_forall_lintegral_and_integral_eq_mul_prod_of_forall_prod_archSemiLocalIdele
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/e12db461-3221-5f33-91ae-9d09ca44517e
-- title:
--   Collecting the archimedean factors of a factorising idele measure
-- statement:
--   Let $L/K$ be an extension of number fields, $S_\tau$ a finite set of primes of $\mathcal O_K$, $\tau$ a Borel measure on the idele group $(\mathbb A_L)^\times$, and let $\tau_{\mathrm{fin},v}$, $\tau_{\mathrm{arch},v}$ be measures on $(L\otimes_K K_v)^\times$ for each prime $v$ and on $(\prod_{w\mid v}L_w)^\times$ for each infinite place $v$ of $K$, together with a chosen unit $\pi_v\in (L\otimes_K K_v)^\times$ for each prime $v$. Assume: for $v\notin S_\tau$, $\tau_{\mathrm{fin},v}$ is a Haar measure restricted to, and normalised by its volume on, the subgroup `integralUnits` of units of the image of $\mathcal O_L\otimes_{\mathcal O_K}\mathcal O_{K_v}$; for $v\in S_\tau$, $\tau_{\mathrm{fin},v}$ is the $\pi_v$-translate of the image of a Haar measure of the kernel of $v$-adic valuation composed with the norm to $K_v$; for infinite $v$, $\tau_{\mathrm{arch},v}$ is the image of a Haar measure of the kernel of the absolute norm to $K_v$; and for every finite $S_f\supseteq S_\tau$, $\tau$-integration of a product $\prod_{v\mid\infty}g_v\cdot\prod_{v\in S_f}f_v$ of measurable $[0,\infty]$-valued functions of the semilocal components, cut off by the indicator of the ideles whose components at $v\notin S_f$ are integral units, factors as $\prod_{v\mid\infty}\int g_v\,d\tau_{\mathrm{arch},v}\cdot\prod_{v\in S_f}\int f_v\,d\tau_{\mathrm{fin},v}$. Then there is a $\sigma$-finite Borel measure $\tau_A$ on $(\mathbb A_{L,\infty})^\times$ such that: $\int\prod_{v\mid\infty}g_v(\text{$v$-component of }y)\,d\tau_A=\prod_v\int g_v\,d\tau_{\mathrm{arch},v}$ for measurable $g_v\ge 0$; for every finite $S_f\supseteq S_\tau$ the same cut-off product with a single measurable $g\colon(\mathbb A_{L,\infty})^\times\to[0,\infty]$ evaluated at the infinite part of $t$ integrates to $\int g\,d\tau_A\cdot\prod_{v\in S_f}\int f_v\,d\tau_{\mathrm{fin},v}$; and, for complex-valued $g$ integrable for $\tau_A$ and $f_v$ integrable for $\tau_{\mathrm{fin},v}$, the corresponding cut-off product is $\tau$-integrable with the same factorisation of its integral.
--
--   This is the step that replaces the separate archimedean factors $\prod_{v\mid\infty}\tau_{\mathrm{arch},v}$ of a factorising measure on the idele group by one measure on the units of the infinite adele ring, and upgrades the factorisation from products of place-by-place functions to arbitrary functions of the archimedean part, in both the $[0,\infty]$-valued and the integrable complex-valued form. It is used in the computation of twisted orbital integrals, where the archimedean variable is handled as a single unit of $\mathbb A_{L,\infty}$ while the finite variables remain semilocal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TransversalMeasure_exists_forall_lintegral_and_integral_eq_mul_prod_of_forall_prod_archSemiLocalIdele.lean

import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel

theorem AutomorphicForm.TransversalMeasure.exists_forall_lintegral_and_integral_eq_mul_prod_of_forall_prod_archSemiLocalIdele
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ : @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ →
      ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin v = (μ (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
    (hbad : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ →
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin v = Measure.map (fun x => πs v * x) (Measure.map Subtype.val μN))
    (harch : ∀ v : InfinitePlace K,
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch v = Measure.map Subtype.val μN)
    (hfac : ∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂τ =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin v)) :
    ∃ τA : @Measure (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ),
      @SigmaFinite (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ) τA ∧
      (∀ g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞, (∀ v, Measurable (g v)) →
        ∫⁻ y, ∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archFibre K L v y) ∂τA =
          ∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch v)) ∧
      (∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
        ∀ (g : (InfiniteAdeleRing L)ˣ → ℝ≥0∞)
          (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞),
          @Measurable _ _ (borel (InfiniteAdeleRing L)ˣ) _ g → (∀ v ∈ Sf, Measurable (f v)) →
          ∫⁻ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
              (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
              Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                  AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                    AutomorphicForm.TransversalMeasure.integralUnits K L v}
                (fun _ => (1 : ℝ≥0∞)) t ∂τ =
            (∫⁻ y, g y ∂τA) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin v)) ∧
      ∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
        ∀ (g : (InfiniteAdeleRing L)ˣ → ℂ)
          (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℂ),
          Integrable g τA → (∀ v ∈ Sf, Integrable (f v) (τfin v)) →
          Integrable (fun t : (AdeleRing (𝓞 L) L)ˣ =>
              g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
                (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
                Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                    AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                      AutomorphicForm.TransversalMeasure.integralUnits K L v}
                  (fun _ => (1 : ℂ)) t) τ ∧
          ∫ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
              (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
              Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                  AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                    AutomorphicForm.TransversalMeasure.integralUnits K L v}
                (fun _ => (1 : ℂ)) t ∂τ =
            (∫ y, g y ∂τA) * ∏ v ∈ Sf, ∫ x, f v x ∂(τfin v) := by sorry
