-- Prove2me | Theorems.Thm_BurkholderDFI_ConcavePhi_theorem_20_1
-- name    : BurkholderDFI.ConcavePhi.theorem_20_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:19.932427+00:00
-- url     : https://prove2.me/theorems/f0134442-9da6-42ab-9de7-11a0125df8b6
-- title:
--   Theorem 20.1 — for concave Φ and nonnegative z_k, EΦ(Σ z_k) ≤ 2EΦ(Σ E(z_k | 𝒜_{k−1}))
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space and $\mathcal A_0\subseteq\mathcal A_1\subseteq\cdots$ sub-$\sigma$-fields of $\mathcal A$. Let $\Phi:[0,\infty]\to[0,\infty]$ be non-decreasing and continuous with $\Phi(0)=0$, satisfying the growth condition $\Phi(2\lambda)\le c\,\Phi(\lambda)$ (6.1), and concave on $[0,\infty)$. Let $z_1,z_2,\dots$ be nonnegative measurable functions on $(\Omega,\mathcal A,P)$. Then
--
--   $$E\Phi\Bigl(\sum_{k=1}^\infty z_k\Bigr)\le 2E\Phi\Bigl(\sum_{k=1}^\infty E(z_k\mid\mathcal A_{k-1})\Bigr).\tag{20.1}$$
--
--   This is the concave counterpart of the convexity lemma (Lemma 16.1 of the paper), with the direction reversed: for concave $\Phi$ a sum of nonnegative variables is controlled by the sum of their predictable projections, with the universal constant $2$. It applies with no integrability assumption and with $z_k$ not adapted to the filtration.
--
--   **Formalization Note** "Concave as above" is `IsPhi Φ c` for an arbitrary constant $c$ (the paper notes that concavity makes the growth condition automatic with $c=2$) together with `IsConcavePhi Φ`; the paper's exclusion of $\Phi\equiv0$ is dropped, as the conclusion is then trivial. The $z_k$ take values in $[0,\infty]$ and are $\mathcal A$-measurable. `z (k+1)` is $z_{k+1}$ and `condLExp (ℱ k) P (z (k+1))` is $E(z_{k+1}\mid\mathcal A_k)$: the conditional expectation is the $[0,\infty]$-valued one, which exists for non-integrable nonnegative functions, as in the paper. The constant $2$ does not depend on $\Phi$, $c$, $P$ or the $z_k$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 20.1, (20.1), p. 38

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConcavePhi

/-- Theorem 20.1, p. 38: for `Φ` concave and satisfying the conditions of Section 7, and
nonnegative measurable `z_1, z_2, …`,
`EΦ(Σ_{k=1}^∞ z_k) ≤ 2EΦ(Σ_{k=1}^∞ E(z_k|𝒜_{k−1}))` (20.1). Here `z (k+1)` is `z_{k+1}` and
`condLExp (ℱ k) P (z (k+1))` is `E(z_{k+1}|𝒜_k)`. -/
theorem theorem_20_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0)
    (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c) (hcc : BurkholderDFI.SquareFnLp.IsConcavePhi Φ) (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) :
    ∫⁻ ω, Φ (∑' k, z (k + 1) ω) ∂P
      ≤ 2 * ∫⁻ ω, Φ (∑' k, condLExp (ℱ k) P (z (k + 1)) ω) ∂P := by sorry

end BurkholderDFI.ConcavePhi
