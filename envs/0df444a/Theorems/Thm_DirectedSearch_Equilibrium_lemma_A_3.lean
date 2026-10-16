-- Prove2me | Theorems.Thm_DirectedSearch_Equilibrium_lemma_A_3
-- name    : DirectedSearch.Equilibrium.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:57.593003+00:00
-- url     : https://prove2.me/theorems/ce2e66f2-e61c-47ef-bf3c-81a195489554
-- title:
--   Lemma A.3, p. 35 — one type's own fixed-point equation τ_θ = ū_θ(τ_θ) has exactly one solution
-- statement:
--   Fix one type $\theta$ and the strategies of the opposite side: finitely many opposite types $i$ with meeting rates $\lambda_i\ge0$, arbitrary real thresholds $\tau_i$, and atomless probability laws $F_i$ on $\mathbb R$ with finite mean; let $\delta>0$. Viewing the expected utility of $\theta$ as a function of its own threshold,
--   $$\bar u_\theta(t)=\frac{\sum_{i}\lambda_i\int_{\max(t,\tau_i)}^\infty u\,dF_i}{\delta+\sum_{i}\lambda_i\int_{\max(t,\tau_i)}^\infty dF_i},$$
--   there is exactly one real $t$ with
--   $$t=\bar u_\theta(t).$$
--
--   This makes the best-response map of Appendix A.3 well defined: given the opposite side's thresholds, each type's best-response threshold is the unique solution of its own fixed-point equation.
--
--   **Formalization Note.** Only the first sentence of Lemma A.3 is stated. Its second sentence ("τ_θ is the unique threshold best response") refers to the agent's Markov decision process of Appendix A.1, which is not formalized. Rates are only nonnegative (an assortment may omit types) and the opposite thresholds are arbitrary, as in a step of the best-response iteration. Finite means are implicit in the paper and stated explicitly.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 35, Lemma A.3

import Mathlib
import Definitions.Def_DirectedSearch_Equilibrium_Setting

namespace DirectedSearch.Equilibrium
open MeasureTheory
theorem lemma_A_3 {ι : Type} [Fintype ι] (δ : ℝ) (lam τ' : ι → ℝ) (F : ι → Measure ℝ)
    (hδ : 0 < δ) (hlam : ∀ i, 0 ≤ lam i)
    (hprob : ∀ i, IsProbabilityMeasure (F i)) (hatom : ∀ i, NullSingletonClass (F i))
    (hint : ∀ i, Integrable id (F i)) :
    ∃! t : ℝ, t = ownU δ lam τ' F t := by sorry
end DirectedSearch.Equilibrium
