-- Prove2me | Theorems.Thm_DirectedOpinion_NoMemory_proposition_5
-- name    : DirectedOpinion.NoMemory.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:34.715688+00:00
-- url     : https://prove2.me/theorems/246c4f64-00cd-42c9-85b4-63fab3d02299
-- title:
--   Proposition 5, p. 14 — E[𝓡*|𝓧_∅] = dE[𝓩_∅|𝓧_∅] + cE[𝓩_1] and Var(𝓡*|𝓧_∅) = d²Var(𝓩_∅|𝓧_∅) + d²Σ𝓒_i²Var(𝓩_1)/(1 − ρ₂)
-- statement:
--   Work in the delayed marked Galton–Watson model of the Setting with no memory, $c+d=1$, and assume every vertex has an inbound neighbour almost surely: $P(\mathcal N_\emptyset>0)=P(\mathcal N_1>0)=1$. Then the conditional mean and variance of the root's stationary opinion $\mathcal R^*$ given its own attribute $\boldsymbol{\mathcal X}_\emptyset$ are, almost surely,
--   $$E[\mathcal R^*\mid\boldsymbol{\mathcal X}_\emptyset]=d\,E[\mathcal Z_\emptyset\mid\boldsymbol{\mathcal X}_\emptyset]+c\,E[\mathcal Z_1],$$
--   $$\operatorname{Var}(\mathcal R^*\mid\boldsymbol{\mathcal X}_\emptyset)=d^2\operatorname{Var}(\mathcal Z_\emptyset\mid\boldsymbol{\mathcal X}_\emptyset)+\frac{d^2}{1-\rho_2}\sum_{i=1}^{\mathcal N_\emptyset}\mathcal C_i^2\operatorname{Var}(\mathcal Z_1),$$
--   where $\rho_2=E\big[\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}^2\big]$, $\mathcal Z_\emptyset$ is the root's media signal and $\mathcal Z_1$ that of a non-root node.
--
--   The paper reads polarization off these formulas: a small conditional variance means that individuals with similar attributes end up with similar opinions.
--
--   **Formalization Note.** The paper assumes the hypotheses of Theorem 2 with a delayed marked Galton–Watson tree as local limit. Those hypotheses (strong coupling, Lipschitz media kernel) only identify $\mathcal R^*$ with the typical opinion of large graphs; the statement and its proof concern $\mathcal R^*$ on the limit tree. The Lean statement is made for the tree's root opinion under the Section 5 standing assumptions, which drops the graph sequence. Conditioning is on the σ-algebra of $\boldsymbol{\mathcal X}_\emptyset$; both identities hold almost everywhere, as conditional expectations and variances are defined only up to null sets. The signals use time index $0$ ($\mathcal Z_\emptyset=\mathcal Z_\emptyset^{(0)}$ enters $\mathcal W_\emptyset^{(0)}$; the law of $\mathcal Z_1^{(k)}$ does not depend on $k$). $1-\rho_2\ge1-c^2>0$, so no hypothesis is added; all variables are bounded, so no integrability hypothesis is needed.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 14, Proposition 5

import Mathlib
import Definitions.Def_DirectedOpinion_NoMemory_Setting
open MeasureTheory ProbabilityTheory

namespace DirectedOpinion.NoMemory

/-- Proposition 5, p. 14: conditional mean and variance of 𝓡* given the root's mark 𝓧_∅, a.e. -/
theorem proposition_5 {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : MarkFns M) (X : Label → Ω → M)
    (U : Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hgw : GWModel P mk X U ζ c d) (hcd : c + d = 1)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    (P[Rstar mk X U ζ c d | markSigma X []] =ᵐ[P]
      fun ω => d * P[Z X U ζ [] 0 | markSigma X []] ω + c * ∫ ω', Z X U ζ [0] 0 ω' ∂P) ∧
    (Var[Rstar mk X U ζ c d; P | markSigma X []] =ᵐ[P]
      fun ω => d ^ 2 * Var[Z X U ζ [] 0; P | markSigma X []] ω +
        d ^ 2 / (1 - rho2 P mk X) * (∑ i ∈ Finset.range (mk.N (X [] ω)), mk.C (X [] ω) i ^ 2) *
          variance (Z X U ζ [0] 0) P) := by sorry

end DirectedOpinion.NoMemory
