-- Prove2me | Theorems.Thm_DirectedOpinion_NoMemory_eq_14
-- name    : DirectedOpinion.NoMemory.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:33.336214+00:00
-- url     : https://prove2.me/theorems/0aa31a79-036f-42e4-863f-ae248a2cc320
-- title:
--   Display (14), p. 30 — E[𝓡] = E[𝓩_1] and Var(𝓡) = d²Var(𝓩_1)/(1 − ρ₂)
-- statement:
--   Work in the delayed marked Galton–Watson model of the Setting with $c+d=1$, and assume that a non-root node has at least one inbound neighbour almost surely, $P(\mathcal N_1>0)=1$. Let $\mathcal R=\mathcal R_1$ be the no-memory limiting opinion of the root's first neighbour, display (7). Then
--   $$E[\mathcal R]=E[\mathcal Z_1]\qquad\text{and}\qquad \operatorname{Var}(\mathcal R)=\frac{d^2}{1-\rho_2}\operatorname{Var}(\mathcal Z_1),$$
--   where $\rho_2=E\big[\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}^2\big]$ and $\mathcal Z_1=\mathcal Z_1^{(0)}$ is a media signal of a non-root node.
--
--   These are the first two moments of the special endogenous solution of the smoothing transform; they feed directly into the conditional moments (12)–(13) of the root opinion.
--
--   **Formalization Note.** $\mathcal R$ is `Rsub … [0] 1` (the paper's node 1 is the label `[0]`). The law of $\mathcal Z_1^{(k)}$ does not depend on $k$, and the statement uses $k=0$. The denominator is positive: $\rho_2\le c^2<1$ under the standing assumptions, so no hypothesis is added. Everything is bounded ($|\mathcal Z|\le1$ and $|\mathcal R|\le 1/d$), so the expectations and variances are those of bounded random variables and Lean's junk value 0 for non-integrable functions never applies; no integrability hypothesis is needed. The root's in-degree plays no role here.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 30, proof of Propositions 4 and 5, display (14)

import Mathlib
import Definitions.Def_DirectedOpinion_NoMemory_Setting
open MeasureTheory ProbabilityTheory

namespace DirectedOpinion.NoMemory

/-- Display (14), p. 30: for the neighbours' limiting opinion 𝓡 = 𝓡_1 = `Rsub … [0] 1`,
E[𝓡] = E[𝓩_1] and Var(𝓡) = d²/(1 − ρ₂) Var(𝓩_1). -/
theorem eq_14 {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : MarkFns M) (X : Label → Ω → M)
    (U : Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hgw : GWModel P mk X U ζ c d) (hcd : c + d = 1)
    (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    (∫ ω, Rsub mk X U ζ c d [0] 1 ω ∂P = ∫ ω, Z X U ζ [0] 0 ω ∂P) ∧
    variance (Rsub mk X U ζ c d [0] 1) P =
      d ^ 2 / (1 - rho2 P mk X) * variance (Z X U ζ [0] 0) P := by sorry

end DirectedOpinion.NoMemory
