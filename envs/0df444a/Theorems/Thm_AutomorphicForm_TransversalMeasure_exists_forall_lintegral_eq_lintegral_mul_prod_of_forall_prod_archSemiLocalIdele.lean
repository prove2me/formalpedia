-- Prove2me | Theorems.Thm_AutomorphicForm_TransversalMeasure_exists_forall_lintegral_eq_lintegral_mul_prod_of_forall_prod_archSemiLocalIdele
-- name    : AutomorphicForm.TransversalMeasure.exists_forall_lintegral_eq_lintegral_mul_prod_of_forall_prod_archSemiLocalIdele
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9907b2e2-ba17-526b-8a5e-04206f9ccc43
-- title:
--   Assembling the archimedean factors of a transversal measure
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $S_\tau$ be a finite set of height-one primes of $\mathcal O_K$, let $\tau$ be a Borel measure on the idele units $(\mathbb A_L)^\times$, and for each prime $v$ of $\mathcal O_K$ let $\tau_{\mathrm{fin},v}$ be a Borel measure on $(L\otimes_K K_v)^\times$, for each infinite place $v$ of $K$ let $\tau_{\mathrm{arch},v}$ be a Borel measure on $\bigl(\prod_{w\mid v}L_w\bigr)^\times$ (the product over the infinite places $w$ of $L$ whose restriction to $K$ is $v$), and let $\pi_v\in(L\otimes_K K_v)^\times$ be given. Assume: for $v\notin S_\tau$, $\tau_{\mathrm{fin},v}$ is $\mu(U_v)^{-1}$ times the restriction of some Haar measure $\mu$ to $U_v$, where $U_v=$ `integralUnits` is the unit group of the image of $\mathcal O_L\otimes_{\mathcal O_K}\mathcal O_{K_v}$ in $L\otimes_K K_v$; for $v\in S_\tau$, $\tau_{\mathrm{fin},v}$ is the translate by $\pi_v$ of the pushforward of a Haar measure on the kernel of $v$-valuation composed with $\mathrm{N}_{K_v}$ on $(L\otimes_K K_v)^\times$; for every infinite $v$, $\tau_{\mathrm{arch},v}$ is the pushforward of a Haar measure on the kernel of $|\mathrm{N}_{K_v}|$; and $\tau$ factorises, in the sense that for every finite $S_f\supseteq S_\tau$ and all measurable $f_v,g_v\ge 0$, $$\int \prod_{v\mid\infty}g_v(t_v)\prod_{v\in S_f}f_v(t_v)\,\mathbf 1[t_v\in U_v\ (v\notin S_f)]\,d\tau=\prod_{v\mid\infty}\int g_v\,d\tau_{\mathrm{arch},v}\cdot\prod_{v\in S_f}\int f_v\,d\tau_{\mathrm{fin},v},$$ where $t_v$ denotes `archSemiLocalIdele` respectively `semiLocalIdele` of $t$ at $v$. Then there is a $\sigma$-finite Borel measure $\tau_A$ on $(\mathbb A_{L,\infty})^\times$ such that $\int\prod_{v\mid\infty}g_v(\mathrm{archFibre}_v\,y)\,d\tau_A=\prod_{v\mid\infty}\int g_v\,d\tau_{\mathrm{arch},v}$ for all measurable $g_v\ge0$, and such that for every finite $S_f\supseteq S_\tau$, every measurable $g\ge 0$ on $(\mathbb A_{L,\infty})^\times$ and measurable $f_v\ge0$ ($v\in S_f$), $\int g(t_\infty)\prod_{v\in S_f}f_v(t_v)\,\mathbf 1[t_v\in U_v\ (v\notin S_f)]\,d\tau=\bigl(\int g\,d\tau_A\bigr)\prod_{v\in S_f}\int f_v\,d\tau_{\mathrm{fin},v}$, $t_\infty$ being the infinite component of the idele $t$.
--
--   This is the step that replaces the separate archimedean local factors $\tau_{\mathrm{arch},v}$, indexed by the infinite places of $K$, by a single measure on the archimedean idele units of $L$, so that a factorisation of $\tau$ indexed by places of $K$ becomes a factorisation with one archimedean and finitely many finite factors. It feeds the corresponding statement for $\mathbb R$-valued (Bochner) integrals used in the computation of twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TransversalMeasure_exists_forall_lintegral_eq_lintegral_mul_prod_of_forall_prod_archSemiLocalIdele.lean

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

theorem AutomorphicForm.TransversalMeasure.exists_forall_lintegral_eq_lintegral_mul_prod_of_forall_prod_archSemiLocalIdele
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
      ∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
        ∀ (g : (InfiniteAdeleRing L)ˣ → ℝ≥0∞)
          (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞),
          @Measurable _ _ (borel (InfiniteAdeleRing L)ˣ) _ g → (∀ v ∈ Sf, Measurable (f v)) →
          ∫⁻ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
              (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
              Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                  AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                    AutomorphicForm.TransversalMeasure.integralUnits K L v}
                (fun _ => (1 : ℝ≥0∞)) t ∂τ =
            (∫⁻ y, g y ∂τA) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin v) := by sorry
