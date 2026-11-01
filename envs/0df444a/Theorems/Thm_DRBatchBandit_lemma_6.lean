-- Prove2me | Theorems.Thm_DRBatchBandit_lemma_6
-- name    : DRBatchBandit.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:54.11586+00:00
-- url     : https://prove2.me/theorems/5e1dace4-c472-487e-a8ce-5b56afe597f7
-- title:
--   Lemma 6, p.17 — for laws on a finite set with point masses $\ge\underline b$, the KL dual value moves by at most $\frac{2M}{\underline b}\mathrm{TV}$
-- statement:
--   Let $\mathbf P_1,\mathbf P_2$ be probability measures on $\mathbb R$ supported on a finite set $\mathbb D$ with $|\mathbb D|>1$ and on $[0,M]$ (Assumption 1.3). Suppose $\mathbf P_2(\{v\})\ge\underline b>0$ for every $v\in\mathbb D$ (Assumption 2.2), and let $\delta>0$. When $\mathrm{TV}(\mathbf P_1,\mathbf P_2)<\underline b/2$,
--   $$\Big|\sup_{\alpha\ge0}\{-\alpha\log\mathbf E_{\mathbf P_1}[e^{-Y/\alpha}]-\alpha\delta\}-\sup_{\alpha\ge0}\{-\alpha\log\mathbf E_{\mathbf P_2}[e^{-Y/\alpha}]-\alpha\delta\}\Big|\le\frac{2M}{\underline b}\mathrm{TV}(\mathbf P_1,\mathbf P_2),$$
--   where $\mathrm{TV}(\mathbf P_1,\mathbf P_2)=\sup_A|\mathbf P_1(A)-\mathbf P_2(A)|$ is the total variation distance.
--
--   It is the discrete-case counterpart of Lemmas 5 and A16 in the proof of Theorem 2.
--
--   **Formalization Note** The dual values are those of `dualValue` (extended reals, finite here); the absolute difference is stated as two one-sided inequalities. TV is the published `MarkovChainCLT.tvDist`, the supremum over measurable sets.
--
--   Differences from the source:
--   - encoding: supremum over α ≥ 0 with the α = 0 value defined by Remark 2 as ess inf → supremum over α > 0; reason: Remark 2 (p.11) defines the α = 0 value as the right limit, so the supremum is unchanged
--   - encoding: |V₁ − V₂| ≤ (2M/b) TV → V₁ ≤ V₂ + (2M/b)TV ∧ V₂ ≤ V₁ + (2M/b)TV in EReal; reason: both dual values are finite here; the two inequalities are the absolute-value bound
--   - encoding: P₁, P₂ supported on 𝔻 and satisfying Assumption 1.3 → P₁(𝔻) = P₂(𝔻) = 1 and P₁([0, M]) = P₂([0, M]) = 1; reason: support of a law on ℝ
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Lemma 6, p.17; proof p.49–51. PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_DRBatchBandit_ScalarDual

open MeasureTheory

namespace DRBatchBandit

open MarkovChainCLT

/-- Lemma 6 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.17): suppose `P₁` and `P₂` are
supported on `𝔻` and satisfy Assumption 1.3 (support in `[0, M]`), and `P₂` satisfies Assumption
2.2 (`|𝔻| > 1`, `P₂({v}) ≥ b > 0` for `v ∈ 𝔻`). When `TV(P₁, P₂) < b/2`,
`|sup_{α ≥ 0} {−α log E_{P₁}[exp(−Y/α)] − αδ} − sup_{α ≥ 0} {−α log E_{P₂}[exp(−Y/α)] − αδ}|
  ≤ (2M/b) TV(P₁, P₂)`.

**Formalization Note.** The dual values are `dualValue` (in `EReal`, supremum over `α > 0`;
here both are finite), and the absolute difference is stated as two one-sided inequalities.
`TV` is `MarkovChainCLT.tvDist`, `sup_A |P₁(A) − P₂(A)|` over measurable `A`. -/
theorem lemma_6 (P₁ P₂ : Measure ℝ) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (D : Finset ℝ) (Mrew b δ : ℝ) (hδ : 0 < δ) (hb : 0 < b) (hD : 1 < D.card)
    (h₁D : P₁ (D : Set ℝ) = 1) (h₂D : P₂ (D : Set ℝ) = 1)
    (h₁M : P₁ (Set.Icc 0 Mrew) = 1) (h₂M : P₂ (Set.Icc 0 Mrew) = 1)
    (hmass : ∀ v ∈ D, ENNReal.ofReal b ≤ P₂ {v}) (hTV : tvDist P₁ P₂ < b / 2) :
    dualValue P₁ δ ≤ dualValue P₂ δ + ((2 * Mrew / b * tvDist P₁ P₂ : ℝ) : EReal) ∧
      dualValue P₂ δ ≤ dualValue P₁ δ + ((2 * Mrew / b * tvDist P₁ P₂ : ℝ) : EReal) := by sorry

end DRBatchBandit
