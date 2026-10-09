-- Prove2me | Theorems.Thm_BanditCovariates_SE_theorem_2_1
-- name    : BanditCovariates.SE.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:45.472715+00:00
-- url     : https://prove2.me/theorems/73426918-cbae-4d19-a3c4-f85c33a28cad
-- title:
--   Theorem 2.1, p. 6 — expected regret of successive elimination
-- statement:
--   Consider $K+1\ge2$ arms with independent, identically distributed rewards along each arm's reward stack, bounded in $[0,1]$. Their means $f_1\le\cdots\le f_{K+1}$ have the last arm as the unique best arm. Let $N$ be an integrable random horizon independent of the entire reward stack, with $\mathbb E N=n$. Run round-based successive elimination with integer $T\ge1$ and $\gamma\ge1$. For every $\Delta>0$,
--
--   $$\mathbb E R_N(\widehat\pi)\le392\gamma^2\left(1+\frac nT\right)\frac K\Delta\,\overline{\log}\!\left(\frac{T\Delta^2}{18\gamma^2}\right)+n\Delta^-,$$
--
--   where $\Delta^-$ is the largest arm gap strictly below $\Delta$, or zero if no such gap exists. This gives the expected regret of a policy that does not need to know the realized horizon.
--
--   **Formalization Note** The source writes $\Delta\ge0$ with division by zero interpreted as infinity; the real-valued Lean statement uses $\Delta>0$. The source's prose and proof specify an end-of-round elimination test, which is the policy formalized here. The reward-stack reference explicitly assumes independence across arms, the traditional static model recalled by the paper. The integrability of the regret follows from its bound by the integrable horizon.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 6, Theorem 2.1; pp. 4–5, standing setup and (2.1)

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

namespace BanditCovariates.SE

open MeasureTheory ProbabilityTheory

/-- Theorem 2.1, p. 6. The positive-Δ case of the paper's extended-real convention. -/
theorem theorem_2_1 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (K : ℕ) (hK : 1 ≤ K)
    (Y : Fin (K + 1) → ℕ → Ω → ℝ) (f : Fin (K + 1) → ℝ)
    (hmodel : RegretBandits.Stochastic.IsStochasticBandit P Y f)
    (hbounded : ∀ i k, ∀ᵐ ω ∂P, Y i k ω ∈ Set.Icc (0 : ℝ) 1)
    (hordered : Monotone f)
    (hbest : ∀ i, i ≠ Fin.last K → f i < f (Fin.last K))
    (N : Ω → ℕ) (hNmeas : Measurable N)
    (hNint : Integrable (fun ω => (N ω : ℝ)) P)
    (n : ℝ) (hn : ∫ ω, (N ω : ℝ) ∂P = n)
    (hNindep : IndepFun N
      (fun ω => fun p : Fin (K + 1) × ℕ => Y p.1 p.2 ω) P)
    (T : ℕ) (hT : 1 ≤ T) (γ : ℝ) (hγ : 1 ≤ γ)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    (∫ ω, regret f T γ Y N ω ∂P) ≤
      392 * γ ^ 2 * (1 + n / (T : ℝ)) *
        ((K : ℝ) / Δ) *
          logbar ((T : ℝ) * Δ ^ 2 / (18 * γ ^ 2)) +
        n * deltaMinus f Δ := by sorry

end BanditCovariates.SE
