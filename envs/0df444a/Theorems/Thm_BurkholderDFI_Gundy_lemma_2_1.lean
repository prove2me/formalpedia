-- Prove2me | Theorems.Thm_BurkholderDFI_Gundy_lemma_2_1
-- name    : BurkholderDFI.Gundy.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:39.89874+00:00
-- url     : https://prove2.me/theorems/1a1853a8-8f82-4d2c-ab5f-63fbff8ac8e6
-- title:
--   Lemma 2.1 — $\|S_{\mu-1}(f)\|_2^2+\|f_{\mu-1}\|_2^2\le 2Ef_\mu f_{\mu-1}\le2\lambda\|f\|_1$
-- statement:
--   Let $f=(f_1,f_2,\dots)$ be either a martingale or a nonnegative submartingale relative to $\mathcal A_1,\mathcal A_2,\dots$ on a probability space $(\Omega,\mathcal A,P)$, and suppose $f$ is $L^1$-bounded, so that $f_\infty=\lim_n f_n$ exists almost everywhere. For $\lambda>0$ let
--   $$\mu=\inf\{n\ge1:|f_n|>\lambda\}\qquad(\inf\emptyset=\infty)$$
--   be the first time $|f_n|$ exceeds $\lambda$. Then
--   $$\|S_{\mu-1}(f)\|_2^2+\|f_{\mu-1}\|_2^2\le 2E f_\mu f_{\mu-1}\le 2\lambda\|f\|_1,$$
--   and equality holds on the left when $f$ is a martingale. Here $S_{\mu-1}(f)$ is the square function stopped just before $\mu$, $f_{\mu-1}$ is the last value before the exit (with $f_0=0$, and $f_{\mu-1}=f_\infty$, $S_{\mu-1}(f)=S(f)$ on $\{\mu=\infty\}$), and $\|f\|_1=\sup_n E|f_n|$.
--
--   The lemma refines Austin's theorem that $S^2(f)$ is integrable on $\{f^*\le\lambda\}$. It is the basis of the elementary proofs of the square-function inequalities of §3, of Gundy's decomposition in §4, and of the exponential estimates of §18.
--
--   **Formalization Note** The limit $f_\infty$ is supplied as a function together with the hypothesis that $f_n\to f_\infty$ almost everywhere. $\mu$ takes values in $\mathbb N\cup\{\infty\}$, and $\mu-1$ is truncated subtraction there ($\infty-1=\infty$; since $\mu\ge1$, $\mu-1=0$ reads $f_0=0$, $S_0(f)=0$). The left side is computed in $[0,\infty]$; the expectation $Ef_\mu f_{\mu-1}$ is a real (Bochner) integral, which the paper shows to be integrable ($|f_{\mu-1}|\le\lambda$ and $f_\mu\in L^1$); were it not integrable, Lean's default value $0$ would only make the first inequality harder. $\|f\|_1$ is finite by hypothesis and is used as a real number on the right. Mathlib's index $0$ and "nonnegative" (almost surely) follow the shared conventions.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 2.1, (2.1), p. 21

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.Gundy

/-- Lemma 2.1, (2.1), p. 21: for `μ = inf {n : |f_n| > λ}`,
`‖S_{μ−1}(f)‖₂² + ‖f_{μ−1}‖₂² ≤ 2E f_μ f_{μ−1} ≤ 2λ‖f‖₁`, with equality on the left in the
martingale case. -/
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

end BurkholderDFI.Gundy
