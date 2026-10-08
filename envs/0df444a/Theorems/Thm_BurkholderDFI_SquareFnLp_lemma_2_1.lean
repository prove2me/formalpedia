-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_lemma_2_1
-- name    : BurkholderDFI.SquareFnLp.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:54:19.59043+00:00
-- url     : https://prove2.me/theorems/4f79cd1e-0a27-4525-84b6-f37739062392
-- title:
--   Lemma 2.1 — ‖S_{μ−1}(f)‖₂² + ‖f_{μ−1}‖₂² ≤ 2Ef_μf_{μ−1} ≤ 2λ‖f‖₁, with equality on the left for martingales
-- statement:
--   Let $f = (f_1, f_2, \dots)$ be a martingale or a nonnegative submartingale relative to $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$, and assume $f$ is $L^1$-bounded, $\|f\|_1 = \sup_{n\ge1} E|f_n| < \infty$; let $f_\infty = \lim_n f_n$, which exists almost everywhere. For $\lambda > 0$ let
--   $$\mu(\omega) = \inf\{n \ge 1 : |f_n(\omega)| > \lambda\}, \qquad \inf\emptyset = \infty,$$
--   with $f_0 = 0$, $S_0(f) = 0$, $S_\infty(f) = S(f)$ and $\infty - 1 = \infty$. Then
--   $$\|S_{\mu-1}(f)\|_2^2 + \|f_{\mu-1}\|_2^2 \le 2E f_\mu f_{\mu-1} \le 2\lambda \|f\|_1, \tag{2.1}$$
--   and equality holds on the left when $f$ is a martingale.
--
--   This identity is the engine of the paper's first chapter: it gives the weak-type bound (3.1) for the square function, Gundy's decomposition, and the exponential bounds of §18.
--
--   **Formalization Note** The paper states that $f_\infty$ exists; here an almost-everywhere limit `fInf` is a parameter, together with the hypothesis that $f_n \to f_\infty$ almost everywhere (any version of the limit gives the same integrals). The left-hand norms are computed in $[0, \infty]$; $E f_\mu f_{\mu-1}$ is a real (Bochner) integral, which is finite because $|f_{\mu-1}| \le \lambda$ and $f_\mu \in L^1$. The Mathlib convention at index $0$ is as in (1.1).
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 2.1, p. 21, display (2.1)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem lemma_2_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : pNorm P 1 f < ⊤) (fInf : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω)))
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ ω, sqFnAt f (exitTime f l ω - 1) ω ^ 2 ∂P
        + ∫⁻ ω, ENNReal.ofReal (valAt f fInf (exitTime f l ω - 1) ω ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * ∫ ω, valAt f fInf (exitTime f l ω) ω
                                 * valAt f fInf (exitTime f l ω - 1) ω ∂P)) ∧
    (2 * ∫ ω, valAt f fInf (exitTime f l ω) ω * valAt f fInf (exitTime f l ω - 1) ω ∂P
      ≤ 2 * l * (pNorm P 1 f).toReal) ∧
    (Martingale f ℱ P →
      ∫⁻ ω, sqFnAt f (exitTime f l ω - 1) ω ^ 2 ∂P
          + ∫⁻ ω, ENNReal.ofReal (valAt f fInf (exitTime f l ω - 1) ω ^ 2) ∂P
        = ENNReal.ofReal (2 * ∫ ω, valAt f fInf (exitTime f l ω) ω
                                   * valAt f fInf (exitTime f l ω - 1) ω ∂P)) := by sorry

end BurkholderDFI.SquareFnLp
