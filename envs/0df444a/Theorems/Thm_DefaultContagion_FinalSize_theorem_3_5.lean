-- Prove2me | Theorems.Thm_DefaultContagion_FinalSize_theorem_3_5
-- name    : DefaultContagion.FinalSize.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:25.340589+00:00
-- url     : https://prove2.me/theorems/3bec0117-2f0c-4149-b3a4-d53bf60cec74
-- title:
--   Theorem 3.5, p. 12 (covariance corrected) — joint process CLT for solvent classes
-- statement:
--   For any finite family of admissible triples $(x,\theta,\ell)$ with $1\le\theta\le d_x^+$ and $0\le\ell<\theta$, consider the processes of solvent class counts, each stopped at a random time $\tau_n\le\tau_n^*$ converging in probability to $t_0>0$. Under Assumptions 1, 2, 3a and 3b, the jointly centred and $n^{-1/2}$-scaled vector of these processes converges in distribution in the Skorokhod $J_1$ path space to a continuous centred Gaussian process stopped at $t_0$:
--   $$n^{-1/2}\bigl(S_{x,\theta,\ell}^{(n)}(t\wedge\tau_n)-n s_{x,\theta,\ell}^{(n)}(e^{-(t\wedge\tau_n)})\bigr)\Rightarrow Z_{x,\theta,\ell}(t\wedge t_0).$$
--   At each $t\le t_0$, the covariance of any two coordinates is the corrected per-bank covariance $\sum_x\mu_x\operatorname{Cov}_x(g_i,g_j)$ at survival probability $e^{-t}$, with $g_i$ the indicator for its type, threshold and number of dead incoming balls. Finite-family convergence is the paper's meaning of joint convergence over a countable collection.
--
--   **Formalization Note** The random times need not be stopping times. The published `PuhaWardFluid.Limit.ConvInDist` definition expresses path convergence through a common-space $J_1$ coupling. The covariance corrects the factor of two error in the printed lifetime term of (26).
-- source:
--   Amini, Cao & Sulem, arXiv:2104.00248v1, p. 12, Theorem 3.5 and equations (25)–(26); corrected covariance

import Mathlib
import Definitions.Def_DefaultContagion_FinalSize_Model
import Definitions.Def_PuhaWardFluid_Limit_Paths

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DefaultContagion.FinalSize

/-- Theorem 3.5, p. 12: joint process convergence for every finite family of
type-threshold-neighbour counts, with the corrected equal-time covariance. -/
theorem theorem_3_5 {X : Type*} [Countable X] [DecidableEq X]
    (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (qn : ℕ → X → ℕ → ℝ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (h2 : Assumption2 dp typ qn mu q)
    (h3a : Assumption3a dp dm typ mu)
    (h3b : Assumption3b dp dm typ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : (n : ℕ) → Fin n → Ω → ℕ)
    (T : (n : ℕ) → Fin n → ℕ → Ω → ℝ)
    (hP : IsDeathProcess P dp typ qn Θ T)
    (τ : ℕ → Ω → ℝ)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτ : ∀ n ω, τ n ω ≤ tauStar dp dm typ Θ T n ω)
    (t0 : ℝ) (ht0 : 0 < t0)
    (hτlim : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => P {ω | ε ≤ |τ n ω - t0|}) atTop (𝓝 0))
    (m : ℕ) (tr : Fin m → X × ℕ × ℕ)
    (htr : ∀ i, 1 ≤ (tr i).2.1 ∧ (tr i).2.1 ≤ dp (tr i).1 ∧
      (tr i).2.2 < (tr i).2.1) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
      (Z : Ω' → ℝ≥0 → EuclideanSpace ℝ (Fin m)),
      IsProbabilityMeasure P' ∧
      (∀ᵐ ω ∂P', Continuous (Z ω)) ∧
      IsGaussianProcess (fun t ω => Z ω t) P' ∧
      (∀ t i, ∫ ω, Z ω t i ∂P' = 0) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ t0 → ∀ i j,
        covariance (fun ω => Z ω t i) (fun ω => Z ω t j) P' =
          limCov dp mu q
            (featX dp (tr i).1 (tr i).2.1 (tr i).2.2)
            (featX dp (tr j).1 (tr j).2.1 (tr j).2.2)
            (Real.exp (-(t : ℝ)))) ∧
      PuhaWardFluid.Limit.ConvInDist (fun a b => dist a b) P
        (fun n ω t => (EuclideanSpace.equiv (Fin m) ℝ).symm fun i =>
          let u : ℝ := min (t : ℝ) (τ n ω)
          (Sxtl dp typ Θ T n (tr i).1 (tr i).2.1 (tr i).2.2 u ω -
            n * sFun dp (muN typ n) (qn n)
              (tr i).1 (tr i).2.1 (tr i).2.2 (Real.exp (-u))) /
            Real.sqrt n)
        P' (fun ω t => Z ω (min t t0.toNNReal)) := by sorry

end DefaultContagion.FinalSize
