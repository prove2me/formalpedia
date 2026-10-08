-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_doob_1_1
-- name    : BurkholderDFI.SquareFnLp.doob_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:54:00.368426+00:00
-- url     : https://prove2.me/theorems/a8b67731-c776-45fe-93cd-07125fed69d1
-- title:
--   (1.1) — Doob's maximal inequality λP(f_n* > λ) ≤ ∫_{f_n* > λ} |f_n| ≤ ‖f‖₁ (cited)
-- statement:
--   Let $f = (f_1, f_2, \dots)$ be a martingale, or a nonnegative submartingale, relative to a filtration $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$ on a probability space $(\Omega, \mathcal A, P)$. Write $f_n^* = \max_{1 \le k \le n} |f_k|$ and $\|f\|_1 = \sup_{n \ge 1} E|f_n|$. Then for every positive integer $n$ and every $\lambda > 0$,
--   $$\lambda\, P(f_n^* > \lambda) \le \int_{\{f_n^* > \lambda\}} |f_n|\, dP \le \|f\|_1.$$
--
--   This is Doob's maximal inequality, quoted by Burkholder from Doob's *Stochastic Processes*; it supplies the term $\lambda P(f^* > \lambda) \le \|f\|_1$ in the proof of the weak-type inequality (3.1), and the first term in the proof of Lemma 3.1.
--
--   **Formalization Note** The paper's martingale relative to $\mathcal A_1, \mathcal A_2, \dots$ is a Mathlib martingale indexed by $\mathbb N$; Mathlib additionally relates the value at index $0$ to $f_1$, which is no restriction (set $f_0 := E(f_1 \mid \mathcal A_0)$) and is never read by the statement. "Nonnegative" means $f_n \ge 0$ almost everywhere for $n \ge 1$. Probabilities, integrals and $\|f\|_1$ are in $[0, \infty]$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §1, p. 20, display (1.1) (cited from Doob [15])

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem doob_1_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (n : ℕ) (hn : 1 ≤ n) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal l * P {ω | ENNReal.ofReal l < maxFnN f n ω}
        ≤ ∫⁻ ω in {ω | ENNReal.ofReal l < maxFnN f n ω}, ENNReal.ofReal |f n ω| ∂P ∧
      ∫⁻ ω in {ω | ENNReal.ofReal l < maxFnN f n ω}, ENNReal.ofReal |f n ω| ∂P ≤ pNorm P 1 f := by sorry

end BurkholderDFI.SquareFnLp
