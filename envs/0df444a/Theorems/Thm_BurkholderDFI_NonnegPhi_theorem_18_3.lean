-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegPhi_theorem_18_3
-- name    : BurkholderDFI.NonnegPhi.theorem_18_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:34.458292+00:00
-- url     : https://prove2.me/theorems/36e53f1e-de1a-4d48-b447-1853f32ee684
-- title:
--   Theorem 18.3 — EΦ(S(f)) ≤ c·EΦ(f*) for nonnegative martingales and every Φ of moderate growth
-- statement:
--   Let $\Phi:[0,\infty]\to[0,\infty]$ be a non-decreasing continuous function with $\Phi(0)=0$ satisfying the growth condition
--   $$\Phi(2\lambda)\le c_{(6.1)}\,\Phi(\lambda),\qquad\lambda>0.$$
--   There is a constant $c$, depending only on $c_{(6.1)}$, such that for every probability space $(\Omega,\mathcal A,P)$, every filtration $(\mathcal A_n)$ and every nonnegative martingale $f=(f_1,f_2,\dots)$,
--   $$E\Phi(S(f))\le c\,E\Phi(f^*),$$
--   where $S(f)=\big(\sum_{k\ge1}d_k^2\big)^{1/2}$ is the square function and $f^*=\sup_n|f_n|$ the maximal function of $f$.
--
--   No convexity of $\Phi$ is assumed. For general martingales the inequality $E\Phi(S(f))\le cE\Phi(f^*)$ holds for convex $\Phi$ but fails for some concave $\Phi$, such as $\Phi(\lambda)=\lambda^p$ with $0<p<1$; nonnegativity of $f$ restores it for every $\Phi$ of moderate growth.
--
--   **Formalization Note** The order of quantifiers is explicit: for every growth constant $c_{(6.1)}$ there is $c>0$ that works for all probability spaces (in `Type`), filtrations, nonnegative martingales and all admissible $\Phi$ simultaneously. The expectations are lower Lebesgue integrals of $[0,\infty]$-valued functions, so both sides may be infinite. Nonnegativity of $f_n$ is almost sure for $n\ge1$, and the index $0$ of the Mathlib martingale is never read (any martingale relative to $\mathcal A_1,\mathcal A_2,\dots$ extends to one). The paper's exclusion of $\Phi\equiv0$ is dropped; the inequality is trivial in that case.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 18.3, (18.3), p. 36

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

/-- Theorem 18.3, p. 36: if `Φ` satisfies the conditions of Section 7 and `f` is a nonnegative
martingale, then `EΦ(S(f)) ≤ cEΦ(f^*)`, where `c` depends only on the growth constant `c_(6.1)`. -/
theorem theorem_18_3 (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P → (∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P := by sorry

end BurkholderDFI.NonnegPhi
