-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar
-- name    : AutomorphicForm.exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/8ff7865d-c9ce-5aeb-8b0a-fc2e6b385f63
-- title:
--   Maximal compact Haar measure factorises over semi-local places
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra. The assertion is the existence of a measure $\kappa$ on $\mathrm{GL}_2$ of the infinite adele ring of $L$, taken with its Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57), with three properties. First, $\kappa$ is a probability measure. Second, $\kappa$ is the pushforward of `maximalCompactHaar L` — the Haar measure of total mass $1$ on the subgroup `adelicMaximalCompact L` of $\mathrm{GL}_2(\mathbb{A}_L)$ consisting of those $k$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at each infinite place $w$ satisfies `IsRowIsometry`, i.e. has determinant of norm $1$ and preserves $\|x\|^2+\|y\|^2$ under the two indicated row combinations — along $k \mapsto$ `glArch`$(k)$. Third, for every finite set $S$ of primes $v$ of $\mathcal{O}_K$, every Borel measurable $g$ on $\mathrm{GL}_2(L_\infty)$ with values in $[0,\infty]$, and every family $f_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$ with $f_v$ Borel measurable for $v \in S$,
--   $$\int_{\mathrm{adelicMaximalCompact}} g(k_\infty) \prod_{v \in S} f_v(k_v)\, dk = \Bigl(\int g \, d\kappa\Bigr) \prod_{v \in S} \int_{\mathrm{semiLocalIntegralSet}} f_v \, d\,\mathrm{semiLocalHaar},$$
--   where $k_v$ denotes `semiLocalComponent K L v` applied to `glFin`$(k)$, `semiLocalIntegralSet K L v` is the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ with all entries of $g$ and of $g^{-1}$ in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$, and `semiLocalHaar K L v` is the Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$ giving that set mass $1$.
--
--   This is the factorisation of the Haar probability measure on the standard maximal compact subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ into its archimedean pushforward and the semi-local Haar measures attached to the primes of $K$, in the form needed for computing adelic integrals one place at a time. It is used by [`AutomorphicForm.exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar`](thm.html#AutomorphicForm.exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar), which transfers the identity from lower integrals of $[0,\infty]$-valued functions to Bochner integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.lean

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

theorem AutomorphicForm.exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ κ : @Measure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)),
      @IsProbabilityMeasure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) κ ∧
      κ = @Measure.map (adelicMaximalCompact L) (GL (Fin 2) (InfiniteAdeleRing L)) _
            (AutomorphicForm.glBorelOf (InfiniteAdeleRing L))
            (fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) (maximalCompactHaar L) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : GL (Fin 2) (InfiniteAdeleRing L) → ℝ≥0∞)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞),
        @Measurable _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) _ g →
        (∀ v ∈ S, @Measurable _ _ (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)) _ (f v)) →
        ∫⁻ k, g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
          ∂(maximalCompactHaar L) =
        (∫⁻ x, g x ∂κ) *
          ∏ v ∈ S, ∫⁻ y in AutomorphicForm.semiLocalIntegralSet K L v, f v y ∂(AutomorphicForm.semiLocalHaar K L v) := by sorry
