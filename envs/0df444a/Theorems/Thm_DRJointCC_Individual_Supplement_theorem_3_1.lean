-- Prove2me | Theorems.Thm_DRJointCC_Individual_Supplement_theorem_3_1
-- name    : DRJointCC.Individual.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:33:15.349852+00:00
-- url     : https://prove2.me/theorems/319216d0-1bcf-4ab0-b94d-b2eda78929d5
-- title:
--   Theorem 3.1 (Bonferroni Approximation), p. 14 — for every safety-factor vector in ℰ, the Bonferroni set lies inside the robust joint feasible set
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   Consider the joint chance constraint with rows $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$, $i=1,\dots,m$, its feasible set
--
--   $$
--   \mathcal X^{\mathrm{JCC}}=\Big\{x\in\mathbb R^n:\ \inf_{\mathbb P\in\mathcal P}\mathbb P\big(y_i^0(x)+y_i(x)^\top\tilde\xi\le0\ \ \forall i=1,\dots,m\big)\ge1-\epsilon\Big\},
--   $$
--
--   the safety factors $\mathcal E=\{\boldsymbol\epsilon\in\mathbb R^m_+:\sum_i\epsilon_i\le\epsilon\}$, and the Bonferroni approximation $\mathcal Z_B^{\mathrm{JCC}}(\boldsymbol\epsilon)$ (p. 14). Then for every $\boldsymbol\epsilon\in\mathcal E$,
--
--   $$
--   \mathcal Z_B^{\mathrm{JCC}}(\boldsymbol\epsilon)\subseteq\mathcal X^{\mathrm{JCC}}.
--   $$
--
--   Thus splitting the risk budget $\epsilon$ among the rows and imposing one LMI-representable individual constraint per row is a safe approximation of the joint chance constraint.
--
--   Differences from the source:
--   - reading: β_i + (1/ε_i)⟨Ω, M_i⟩ ≤ 0, undefined at ε_i = 0, which ℰ allows → ε_i β_i + ⟨Ω, M_i⟩ ≤ 0 and β_i ≤ 0; reason: equivalent for ε_i > 0 since ⟨Ω, M_i⟩ ≥ 0; at ε_i = 0 it is the extended-real reading ((1/0)·0 = 0, (1/0)·t = +∞ for t > 0), and it avoids Lean's 1/0 = 0, which would make row i vacuous and the theorem false
--   - encoding: inf_P P(·) ≥ 1 − ε → ENNReal.ofReal (1 − ε) ≤ ⨅ P ∈ 𝒫, P(·) in ℝ≥0∞ (published XJCC); reason: Lean convention; same instances
--   - encoding: M ∈ 𝕊^{k+1}, M ≽ 0, blocks indexed 1..k+1 → Matrix.PosSemidef (which includes symmetry) on Fin k ⊕ Unit with the extra index last; reason: Lean convention; same instances
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 14, Theorem 3.1 (with ℰ, (26) and Z_B^JCC(𝛜)); p. 13, X^JCC

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_Bonferroni

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- Theorem 3.1 (Bonferroni Approximation), p. 14: for every vector of safety factors
`𝛜 ∈ ℰ` (`ε_i ≥ 0`, `Σ_i ε_i ≤ ε`), `𝒵_B^JCC(𝛜) ⊆ 𝒳^JCC`. -/
theorem theorem_3_1 {m n k : ℕ} (D : DRJointCC.Joint.JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (e : Fin m → ℝ) (he : e ∈ safetyFactors m ε) :
    ZB D μ Sig e ⊆ DRJointCC.Joint.XJCC D μ Sig ε := by sorry

end DRJointCC.Individual.Supplement
