-- Prove2me | Theorems.Thm_DirectedSearch_Approx_lemma_4_5
-- name    : DirectedSearch.Approx.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:08.31972+00:00
-- url     : https://prove2.me/theorems/453f0650-d17d-4356-a25f-2d8438da1a9d
-- title:
--   Lemma 4.5, p. 21 — ρ = max_{τ≥0} A(τ) is a fixed point of A, and A is unimodal around it
-- statement:
--   Let $F$ be a probability law on $\mathbb R$ with no atoms and finite mean, let $\delta>0$, and define
--   $$A(\tau)=\frac{\int_\tau^\infty u\,dF}{\delta+\int_\tau^\infty dF},\qquad \rho=\max_{\tau\ge0}A(\tau).$$
--   Then
--
--   1. the maximum is attained: $A(\tau)=\rho$ for some $\tau\ge0$;
--   2. $A(\rho)=\rho$;
--   3. $A$ is (weakly) increasing on $(-\infty,\rho]$ and (weakly) decreasing on $[\rho,\infty)$.
--
--   The lemma shows that the first-best threshold of a pair can be set to $\rho_{mw}$, and it is the monotonicity used to compare idealized and first-best thresholds.
--
--   **Formalization Note.** $\rho$ is defined as the supremum of $A$ over $[0,\infty)$, never as a fixed point; attainment is part of the conclusion. Monotonicity is weak, since $A$ is constant where $F$ has no mass. "Continuous distribution" is read as atomless; no density is assumed. Finite mean is a disclosed addition (the paper uses the integrals as real numbers).
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 21, Lemma 4.5

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

namespace DirectedSearch.Approx
open MeasureTheory
theorem lemma_4_5 (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hint : Integrable id μ) (δ : ℝ) (hδ : 0 < δ) :
    let ρ := sSup (ratio μ δ '' Set.Ici 0)
    (∃ τ, 0 ≤ τ ∧ ratio μ δ τ = ρ) ∧ ratio μ δ ρ = ρ ∧
      MonotoneOn (ratio μ δ) (Set.Iic ρ) ∧ AntitoneOn (ratio μ δ) (Set.Ici ρ) := by sorry
end DirectedSearch.Approx
