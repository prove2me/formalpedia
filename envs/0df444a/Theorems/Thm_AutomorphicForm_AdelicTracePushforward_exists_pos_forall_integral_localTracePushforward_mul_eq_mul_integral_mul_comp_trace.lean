-- Prove2me | Theorems.Thm_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace
-- name    : AutomorphicForm.AdelicTracePushforward.exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1d6b8f70-f7af-5876-ac28-0e3ad52c171c
-- title:
--   Local trace push-forward is adjoint to composition with the trace
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, so that one has the completion $K_v$ and the $K_v$-algebra $L \otimes_K K_v$; both are equipped with measurable structures for which the Borel sets are the measurable sets, $\mu$ is an additive Haar measure on $K_v$ and $\nu$ is an additive Haar measure on $L \otimes_K K_v$. The assertion is that there is a real constant $c > 0$, depending only on these data and not on the test functions, such that for every $\Phi : L \otimes_K K_v \to \mathbb{C}$ and every $g : K_v \to \mathbb{C}$ with $\Phi$ locally constant and of compact support and $g$ locally integrable with respect to $\mu$, the following three statements hold: the function $r \mapsto \Phi^{\flat}(r)\,g(r)$ is integrable for $\mu$; the function $x \mapsto \Phi(x)\,g(\mathrm{Tr}_{(L \otimes_K K_v)/K_v}(x))$ is integrable for $\nu$; and $$\int_{K_v} \Phi^{\flat}(r)\,g(r)\,d\mu(r) = c \int_{L \otimes_K K_v} \Phi(x)\, g\bigl(\mathrm{Tr}_{(L \otimes_K K_v)/K_v}(x)\bigr)\,d\nu(x).$$ Here $\Phi^{\flat} =$ `localTracePushforward K L v Φ` is the fibre integral $$\Phi^{\flat}(r) = \int \Phi\Bigl( (\,[L:K]\,)^{-1} \otimes r + \sum_i b_i \otimes w_i \Bigr)\,dw,$$ where $[L:K]^{-1}$ is the inverse in $L$ of the image of $\operatorname{finrank}_K L$, the $b_i$ are the members of the chosen finite $K$-basis of $\ker(\mathrm{Tr}_{L/K})$, and $w$ ranges over $K_v^{\,d}$, $d = \dim_K \ker(\mathrm{Tr}_{L/K})$, with respect to the product of $d$ copies of the canonical additive Haar measure on $K_v$ normalised so that the valuation ring $\mathcal{O}_v$ has measure $1$.
--
--   This is the change-of-variables (adjointness) identity relating the push-forward of a locally constant compactly supported function along the trace map of $L \otimes_K K_v$ over $K_v$ with integration against a function pulled back along that trace, the Haar normalisations being absorbed into a single positive constant. It is used in the analysis of twisted unipotent contributions, in the derivation of the derivative of a local zeta factor at $1$ in terms of weighted moments at unramified places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.AdelicTracePushforward.exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ (Φ : L ⊗[K] v.adicCompletion K → ℂ) (g : v.adicCompletion K → ℂ),
      IsLocallyConstant Φ → HasCompactSupport Φ → LocallyIntegrable g μ →
      Integrable (fun r => AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r * g r) μ ∧
      Integrable (fun x => Φ x * g (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x)) ν ∧
      ∫ r, AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r * g r ∂μ =
        (c : ℂ) * ∫ x, Φ x * g (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) ∂ν := by sorry
