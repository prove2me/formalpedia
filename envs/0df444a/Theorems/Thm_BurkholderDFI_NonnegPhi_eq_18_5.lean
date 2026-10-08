-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegPhi_eq_18_5
-- name    : BurkholderDFI.NonnegPhi.eq_18_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:40.412982+00:00
-- url     : https://prove2.me/theorems/f89a0644-a686-4cdb-a220-ddcf6df0c296
-- title:
--   (18.5) — ∫_{a+λ²}^∞ P(S²_{μ−1}(f) > s) ds ≤ 2λ² P(S²_{μ−1}(f) > a) for nonnegative martingales
-- statement:
--   Let $f=(f_1,f_2,\dots)$ be a nonnegative martingale on a probability space $(\Omega,\mathcal A,P)$ with respect to a filtration $(\mathcal A_n)$. Fix $\lambda>0$ and let $\mu=\inf\{n\ge1:|f_n|>\lambda\}$ (with $\inf\emptyset=\infty$), so that $S_{\mu-1}(f)=\big(\sum_{k<\mu}d_k^2\big)^{1/2}$ is the square function of $f$ stopped just before $|f_n|$ first exceeds $\lambda$. Then for every $a>0$,
--   $$\int_{a+\lambda^2}^\infty P\big(S_{\mu-1}^2(f)>s\big)\,ds\le 2\lambda^2\,P\big(S_{\mu-1}^2(f)>a\big).$$
--
--   The inequality says that the tail of $S_{\mu-1}^2(f)$ beyond $a+\lambda^2$ has total mass controlled by $2\lambda^2$ times the probability of exceeding $a$. In the paper it yields both the exponential square integrability of $S_{\mu-1}(f)$ (Theorem 18.1) and, with $\lambda$ replaced by $\delta\lambda$ and $a=\lambda^2$, the good-$\lambda$ inequality of Theorem 18.2.
--
--   **Formalization Note** $S_{\mu-1}^2(f)$ takes values in $[0,\infty]$, with $S_{\mu-1}(f)=S(f)$ on $\{\mu=\infty\}$ and $S_0(f)=0$; the integral over $s$ is a Lebesgue integral of the nonnegative function $s\mapsto P(S^2_{\mu-1}(f)>s)$. Nonnegativity of $f_n$ is almost sure for $n\ge1$; the index $0$ of the Mathlib martingale is never read.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (18.5), proof of Theorem 18.1, p. 37

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

/-- (18.5), proof of Theorem 18.1, p. 37: for a nonnegative martingale `f` and
`μ = inf {n : |f_n| > λ}`, `∫_{a+λ²}^∞ P(S²_{μ−1}(f) > s) ds ≤ 2λ² P(S²_{μ−1}(f) > a)`, `a > 0`. -/
theorem eq_18_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (l : ℝ) (hl : 0 < l) (a : ℝ) (ha : 0 < a) :
    ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2}
      ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2} := by sorry

end BurkholderDFI.NonnegPhi
