-- Prove2me | Theorems.Thm_DirectedOpinion_NoMemory_proposition_4
-- name    : DirectedOpinion.NoMemory.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:31.395831+00:00
-- url     : https://prove2.me/theorems/03a8339c-f386-41d3-ad18-9cf3fbf7a71f
-- title:
--   Proposition 4 — without memory on a Galton–Watson limit, E[𝓡*] = dE[𝓩_∅] + cE[𝓩₁] and Var(𝓡*) = d²Var(𝓩_∅) + ρ*₂d²Var(𝓩₁)/(1 − ρ₂)
-- statement:
--   Work in the delayed marked Galton–Watson model of the Setting with no memory, $c+d=1$, and assume every vertex has an inbound neighbour almost surely: $P(\mathcal N_\emptyset>0)=P(\mathcal N_1>0)=1$. Then the root's stationary opinion $\mathcal R^*=\sum_{s\ge0}(\Delta^s\mathcal W^{(s)})(\emptyset)$ has mean and variance
--   $$E[\mathcal R^*]=d\,E[\mathcal Z_\emptyset]+c\,E[\mathcal Z_1],$$
--   $$\operatorname{Var}(\mathcal R^*)=d^2\operatorname{Var}(\mathcal Z_\emptyset)+\frac{\rho_2^*d^2}{1-\rho_2}\operatorname{Var}(\mathcal Z_1),$$
--   where $\rho_2^*=E\big[\sum_{i=1}^{\mathcal N_\emptyset}\mathcal C_i^2\big]$, $\rho_2=E\big[\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}^2\big]$, $\mathcal Z_\emptyset$ is the root's media signal and $\mathcal Z_1$ that of a non-root node.
--
--   By Theorem 2, $\mathcal R^*$ is the opinion of a typical vertex in a large random directed graph. The variance formula says when consensus happens: the stationary opinions concentrate when $d\mathcal Z_\emptyset$ and $d\mathcal Z_1$ have small variance, and the weights enter only through the second moments $\rho_2^*,\rho_2$.
--
--   **Formalization Note.** The paper assumes the hypotheses of Theorem 2 with a delayed marked Galton–Watson tree as local limit. Those hypotheses (strong coupling, Lipschitz media kernel) only identify $\mathcal R^*$ with the typical opinion of large graphs; the statement and its proof concern $\mathcal R^*$ on the limit tree. The Lean statement is made for the tree's root opinion under the Section 5 standing assumptions (independent marks, i.i.d. away from the root, signals $\mathcal W=d\mathcal Z+\mathcal Q(c-\sum\mathcal C)$ with $\mathcal Z\in[-1,1]$ conditionally i.i.d. given the mark, in quantile form), which drops the graph sequence. Child indices are 0-based, so the paper's node 1 is the label `[0]`. Signals use time index $0$; their laws do not depend on time. The denominator is positive since $\rho_2\le c^2<1$, and every variable is bounded ($|\mathcal R^*|\le1/d$), so neither a positivity nor an integrability hypothesis is added; the series defining $\mathcal R^*$ converges absolutely for every outcome. The hypotheses $P(\mathcal N_\emptyset>0)=P(\mathcal N_1>0)=1$ are essential: at a vertex without inbound neighbours the signal carries the extra term $c\,\mathcal Q$ and the formulas change.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 11, Proposition 4

import Mathlib
import Definitions.Def_DirectedOpinion_NoMemory_Setting
open MeasureTheory ProbabilityTheory

namespace DirectedOpinion.NoMemory

/-- Proposition 4, p. 11: with no memory (c + d = 1) on a delayed marked Galton–Watson tree with
P(𝓝_∅ > 0) = P(𝓝_1 > 0) = 1,
E[𝓡*] = d E[𝓩_∅] + c E[𝓩_1] and Var(𝓡*) = d² Var(𝓩_∅) + ρ*₂ d²/(1 − ρ₂) Var(𝓩_1). -/
theorem proposition_4 {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : MarkFns M) (X : Label → Ω → M)
    (U : Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hgw : GWModel P mk X U ζ c d) (hcd : c + d = 1)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    (∫ ω, Rstar mk X U ζ c d ω ∂P =
      d * ∫ ω, Z X U ζ [] 0 ω ∂P + c * ∫ ω, Z X U ζ [0] 0 ω ∂P) ∧
    variance (Rstar mk X U ζ c d) P =
      d ^ 2 * variance (Z X U ζ [] 0) P +
        rho2Star P mk X * d ^ 2 / (1 - rho2 P mk X) * variance (Z X U ζ [0] 0) P := by sorry

end DirectedOpinion.NoMemory
