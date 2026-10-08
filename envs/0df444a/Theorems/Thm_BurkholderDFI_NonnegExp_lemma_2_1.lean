-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegExp_lemma_2_1
-- name    : BurkholderDFI.NonnegExp.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:23.951002+00:00
-- url     : https://prove2.me/theorems/ae520bc0-a245-44d7-b8e2-861e3f6df7c2
-- title:
--   Lemma 2.1 — stopped square-function identity and L¹ bound
-- statement:
--   Let $f=(f_n)_{n\ge1}$ be an $L^1$-bounded martingale or nonnegative submartingale on a probability space, and let $\lambda>0$. Put $\mu=\inf\{n\ge1:|f_n|>\lambda\}$. Then
--
--   $$
--   \|S_{\mu-1}(f)\|_2^2+\|f_{\mu-1}\|_2^2
--   \le 2E[f_\mu f_{\mu-1}]
--   \le 2\lambda\|f\|_1.
--   $$
--
--   The first inequality is an equality when $f$ is a martingale. This stopped estimate supplies the second-moment control used in §18.
--
--   **Formalization Note** Nonnegativity is almost everywhere at every time $n\ge1$. The paper obtains the almost-everywhere limit $f_\infty$ from $L^1$ boundedness; the statement supplies this limit and its convergence explicitly so that $f_\mu$ is defined when $\mu=\infty$. The index $0$ of Mathlib's martingale is auxiliary; its conditional-expectation constraint imposes no restriction on the paper's process. The extended nonnegative integrals represent squared norms; the middle product is a real integral. In $\mathbb N_\infty$, $\infty-1=\infty$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 2.1, p. 21; https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Lemma 2.1, p. 21. -/
theorem lemma_2_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤) (fInf : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω)))
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ ω, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2 ∂P
        + ∫⁻ ω, ENNReal.ofReal (BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω
                                 * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P)) ∧
    (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P
      ≤ 2 * l * (BurkholderDFI.SquareFnLp.pNorm P 1 f).toReal) ∧
    (Martingale f ℱ P →
      ∫⁻ ω, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2 ∂P
          + ∫⁻ ω, ENNReal.ofReal (BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2) ∂P
        = ENNReal.ofReal (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω
                                   * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P)) := by sorry

end BurkholderDFI.NonnegExp
