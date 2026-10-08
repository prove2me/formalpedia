-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_doob_stopped_L1
-- name    : BurkholderDFI.SquareFnLp.doob_stopped_L1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:54:10.239653+00:00
-- url     : https://prove2.me/theorems/1bd0dd2a-2c3e-48ca-919b-084066046056
-- title:
--   §1 — an L¹-bounded martingale converges a.e. and ‖f_μ‖₁ ≤ ‖f‖₁ for every stopping time μ (cited)
-- statement:
--   Let $f = (f_1, f_2, \dots)$ be a martingale, or a nonnegative submartingale, relative to $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$, and suppose $f$ is $L^1$-bounded: $\|f\|_1 = \sup_{n \ge 1} E|f_n| < \infty$. Then
--
--   1. $f$ converges almost everywhere to a limit $f_\infty$, and
--   2. for every stopping time $\mu$ with values in $\{0, 1, 2, \dots, \infty\}$,
--   $$\|f_\mu\|_1 = E|f_\mu| \le \|f\|_1,$$
--   where $f_\mu(\omega) = f_{\mu(\omega)}(\omega)$, with $f_0 = 0$ and $f_\infty$ the limit from part 1.
--
--   Burkholder takes these facts from Doob; they make $f_\mu$ and $f_{\mu-1}$ well defined and integrable in Lemma 2.1.
--
--   **Formalization Note** The conclusion asserts the existence of an almost-everywhere limit `fInf` such that the bound holds with $f_\infty$ = `fInf`. A stopping time is Mathlib's `IsStoppingTime` with values in $\mathbb N \cup \{\infty\}$, relative to the filtration $\mathcal A_0 \subseteq \mathcal A_1 \subseteq \cdots$ (index $0$ allowed, where $f_0 = 0$). The Mathlib convention at index $0$ is as in (1.1) and is no restriction.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §1, p. 20 (facts cited from Doob [15])

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem doob_stopped_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : pNorm P 1 f < ⊤) (μ : Ω → ℕ∞) (hμ : IsStoppingTime ℱ μ) :
    ∃ fInf : Ω → ℝ, (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) ∧
      ∫⁻ ω, ENNReal.ofReal |valAt f fInf (μ ω) ω| ∂P ≤ pNorm P 1 f := by sorry

end BurkholderDFI.SquareFnLp
