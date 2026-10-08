-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegPhi_lemma_2_1
-- name    : BurkholderDFI.NonnegPhi.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:26.800986+00:00
-- url     : https://prove2.me/theorems/3d636e65-4f5c-4156-b6fb-39b4f20708ce
-- title:
--   Lemma 2.1 — ‖S_{μ−1}(f)‖₂² + ‖f_{μ−1}‖₂² ≤ 2E f_μ f_{μ−1} ≤ 2λ‖f‖₁
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space with a filtration $(\mathcal A_n)$, and let $f=(f_1,f_2,\dots)$ be either a martingale or a nonnegative submartingale that is $L^1$-bounded, $\|f\|_1=\sup_n E|f_n|<\infty$. Let $f_\infty=\lim_n f_n$, which exists almost everywhere. Fix $\lambda>0$ and let
--   $$\mu=\inf\{n\ge1:|f_n|>\lambda\}\qquad(\inf\emptyset=\infty).$$
--   Then
--   $$\|S_{\mu-1}(f)\|_2^2+\|f_{\mu-1}\|_2^2\le 2E f_\mu f_{\mu-1}\le 2\lambda\|f\|_1,$$
--   and in the martingale case the left inequality is an equality. Here $S_0(f)=f_0=0$, and on $\{\mu=\infty\}$, $S_{\mu-1}(f)=S(f)$ and $f_{\mu-1}=f_\mu=f_\infty$.
--
--   This identity controls the square function of a martingale stopped just before it first exceeds $\lambda$, by the $L^1$ norm of the martingale; it is the basic estimate behind the square function inequalities of the paper, and enters this mission through (18.5).
--
--   **Formalization Note** The paper's martingale relative to $\mathcal A_1,\mathcal A_2,\dots$ is a Mathlib martingale indexed by $\mathbb N$ whose value at index $0$ is never read; any paper martingale extends to one by setting the index-$0$ term to $E(f_1\mid\mathcal A_0)$. Nonnegativity is almost sure, for $n\ge1$. The limit $f_\infty$ is a hypothesis-supplied function with almost-everywhere convergence (the paper notes it exists). $\mu-1$ is truncated subtraction on $\{1,2,\dots,\infty\}$, with $\infty-1=\infty$. The expectation $Ef_\mu f_{\mu-1}$ is a real (Bochner) integral; it is finite because $|f_{\mu-1}|\le\lambda$ and $f_\mu$ is integrable.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 2.1, (2.1), p. 21

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

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

end BurkholderDFI.NonnegPhi
