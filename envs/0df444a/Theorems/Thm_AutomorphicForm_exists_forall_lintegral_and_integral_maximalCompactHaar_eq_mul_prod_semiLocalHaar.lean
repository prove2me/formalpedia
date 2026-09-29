-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar
-- name    : AutomorphicForm.exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/4d2a0489-d4c2-5dfe-b256-aef1d14fd5b5
-- title:
--   Product decomposition of Haar measure on the adelic maximal compact
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$. The assertion is the existence of a measure $\kappa$ on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$, for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) of the infinite adele ring of $L$, with the following four properties. First, $\kappa$ is a probability measure. Second, $\kappa$ is the pushforward under $k \mapsto$ `glArch`$(k)$, the archimedean component of $k$ in $\mathrm{GL}_2$, of the Haar measure `maximalCompactHaar L` on the group `adelicMaximalCompact L`, namely the subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ consisting of those $k$ whose finite part lies in `finiteIntegralGL2 (𝓞 L) L` and whose archimedean component at each infinite place $w$ of $L$ satisfies `IsRowIsometry`, i.e. has determinant of absolute value $1$ and acts on row vectors $(x,y)$ preserving $\lVert x\rVert^2+\lVert y\rVert^2$. Third, for every finite set $S$ of height-one primes $v$ of $\mathcal{O}_K$, every measurable $g \colon \mathrm{GL}_2(\mathbb{A}_{L,\infty}) \to [0,\infty]$ and every family $f_v \colon \mathrm{GL}_2(L \otimes_K K_v) \to [0,\infty]$ with $f_v$ measurable for $v \in S$,
--   $$\int^{-} g(\mathrm{glArch}\,k)\prod_{v \in S} f_v\bigl(\mathrm{semiLocalComponent}_v(\mathrm{glFin}\,k)\bigr)\,d(\mathrm{maximalCompactHaar}\,L) = \Bigl(\int^{-} g \,d\kappa\Bigr)\prod_{v \in S}\int^{-}_{\mathrm{semiLocalIntegralSet}_v} f_v \,d(\mathrm{semiLocalHaar}_v),$$
--   where `semiLocalComponent K L v` is the map on $\mathrm{GL}_2$ induced by `semiLocalEval K L v`, `semiLocalIntegralSet K L v` is the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ such that both $g$ and $g^{-1}$ have all entries in the image of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`, and `semiLocalHaar K L v` is the Haar measure of $\mathrm{GL}_2(L \otimes_K K_v)$ normalised to give that compact open set mass one. Fourth, the same identity for Bochner integrals of complex-valued functions: for $S$, $g$ integrable against $\kappa$ and $f_v$ integrable on `semiLocalIntegralSet K L v` against `semiLocalHaar K L v` for $v \in S$, the function $k \mapsto g(\mathrm{glArch}\,k)\prod_{v \in S} f_v(\mathrm{semiLocalComponent}_v(\mathrm{glFin}\,k))$ is integrable for `maximalCompactHaar L` and its integral equals $\bigl(\int g \,d\kappa\bigr)\prod_{v \in S}\int_{\mathrm{semiLocalIntegralSet}_v} f_v \,d(\mathrm{semiLocalHaar}_v)$.
--
--   This is the Fubini-type factorisation of the Haar probability measure on the standard maximal compact subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ into its archimedean factor and the semi-local factors at the finite places of $K$, with the normalisation that each semi-local integral factor gives mass one to the integral points. It extends the $[0,\infty]$-valued statement [`AutomorphicForm.exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar`](thm.html#AutomorphicForm.exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar) by the complex-valued Bochner case, and is used in the computation of twisted orbital integrals over a Bruhat transversal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ κ : @Measure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)),
      @IsProbabilityMeasure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) κ ∧
      κ = @Measure.map (adelicMaximalCompact L) (GL (Fin 2) (InfiniteAdeleRing L)) _
            (AutomorphicForm.glBorelOf (InfiniteAdeleRing L))
            (fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) (maximalCompactHaar L) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : GL (Fin 2) (InfiniteAdeleRing L) → ℝ≥0∞)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞),
        @Measurable _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) _ g →
        (∀ v ∈ S, @Measurable _ _ (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)) _ (f v)) →
        ∫⁻ k, g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
          ∂(maximalCompactHaar L) =
        (∫⁻ x, g x ∂κ) *
          ∏ v ∈ S, ∫⁻ y in AutomorphicForm.semiLocalIntegralSet K L v, f v y ∂(AutomorphicForm.semiLocalHaar K L v)) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        Integrable g κ →
        (∀ v ∈ S, IntegrableOn (f v) (AutomorphicForm.semiLocalIntegralSet K L v) (AutomorphicForm.semiLocalHaar K L v)) →
        Integrable (fun k : adelicMaximalCompact L => g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L))))
          (maximalCompactHaar L) ∧
        ∫ k, g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
          ∂(maximalCompactHaar L) =
        (∫ x, g x ∂κ) *
          ∏ v ∈ S, ∫ y in AutomorphicForm.semiLocalIntegralSet K L v, f v y ∂(AutomorphicForm.semiLocalHaar K L v) := by sorry
