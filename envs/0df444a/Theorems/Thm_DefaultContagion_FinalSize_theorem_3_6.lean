-- Prove2me | Theorems.Thm_DefaultContagion_FinalSize_theorem_3_6
-- name    : DefaultContagion.FinalSize.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:19.721274+00:00
-- url     : https://prove2.me/theorems/c193ff63-d240-4df1-a6f0-c83ea18c26dc
-- title:
--   Theorem 3.6, p. 12 (covariance corrected) — joint process CLT for the five counts
-- statement:
--   Let $\tau_n\le\tau_n^*$ be random times converging in probability to $t_0>0$. Under the paper's threshold, type-frequency and exponential degree-moment assumptions, the vector of the five count processes $S_n,D_n,H_n^+,I_n^+,W_n$, centred at their finite-economy fluid functions and scaled by $n^{-1/2}$, converges jointly in distribution in Skorokhod $J_1$ path space:
--   $$n^{-1/2}\bigl(\boldsymbol\clubsuit_n(t\wedge\tau_n)-n\boldsymbol f^{(n)}(e^{-(t\wedge\tau_n)})\bigr)\Rightarrow\boldsymbol Z(t\wedge t_0).$$
--   The limit is a continuous centred Gaussian vector process. Its equal-time covariance for $0\le t\le t_0$ is the explicit corrected matrix $C(e^{-t})$, formed from the per-bank contributions to all five counts. This process limit supplies the random vector $\boldsymbol Z(t^*)$ in Theorem 3.7.
--
--   **Formalization Note** The five coordinates are ordered $S,D,H^+,I^+,W$ and share one Skorokhod time change. The random times need not be stopping times. The finite $I^+$ and $W$ centring uses $\lambda^{(n)}$. The corrected covariance replaces the printed (41)–(46), whose lifetime variance is too small by a factor of two.
-- source:
--   Amini, Cao & Sulem, arXiv:2104.00248v1, p. 12, Theorem 3.6 and equation (7); corrected covariance to equations (41)–(46)

import Mathlib
import Definitions.Def_DefaultContagion_FinalSize_Model
import Definitions.Def_PuhaWardFluid_Limit_Paths

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DefaultContagion.FinalSize

/-- Theorem 3.6, p. 12: joint process convergence of the five counts, with
the corrected explicit equal-time covariance. -/
theorem theorem_3_6 {X : Type*} [Countable X] [DecidableEq X]
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
      (fun n : ℕ => P {ω | ε ≤ |τ n ω - t0|}) atTop (𝓝 0)) :
    let lam : ℝ := ∑' x, mu x * (dp x : ℝ)
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
      (Z : Ω' → ℝ≥0 → EuclideanSpace ℝ (Fin 5)),
      IsProbabilityMeasure P' ∧
      (∀ᵐ ω ∂P', Continuous (Z ω)) ∧
      IsGaussianProcess (fun t ω => Z ω t) P' ∧
      (∀ t i, ∫ ω, Z ω t i ∂P' = 0) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ t0 → ∀ i j,
        covariance (fun ω => Z ω t i) (fun ω => Z ω t j) P' =
          covMat dp dm mu q (Real.exp (-(t : ℝ))) i j) ∧
      PuhaWardFluid.Limit.ConvInDist (fun a b => dist a b) P
        (fun n ω t => (EuclideanSpace.equiv (Fin 5) ℝ).symm fun c =>
          let u : ℝ := min (t : ℝ) (τ n ω)
          (stateVec dp dm typ Θ T n u ω c -
            n * fVec dp dm (lamN dp typ n) (muN typ n) (qn n)
              (Real.exp (-u)) c) / Real.sqrt n)
        P' (fun ω t => Z ω (min t t0.toNNReal)) := by sorry

end DefaultContagion.FinalSize
