-- Prove2me | Theorems.Thm_DefaultContagion_FinalSize_theorem_3_7
-- name    : DefaultContagion.FinalSize.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:14.98376+00:00
-- url     : https://prove2.me/theorems/c775f93b-072f-48fc-a028-e0c148d01e41
-- title:
--   Theorem 3.7, p. 13 (covariance corrected) — jointly Gaussian final default-cascade counts
-- statement:
--   Consider the §2.4 balls-and-bins death process under Assumptions 1, 2, 3a and 3b. Let $z^*$ be the largest zero of $f_W$ on $[0,1]$, let $\widehat z_n$ be the largest zero of $f_W^{(n)}$, and put $\alpha=f_W'(z^*)$. The final time $\tau_n^*$ is the first time the white infected out-ball count becomes negative.
--
--   1. If $z^*=0$, almost every bank defaults: $D_n(\tau_n^*)/n\xrightarrow{p}1$.
--   2. If $0<z^*\le1$ and $\alpha>0$, then $\widehat z_n\to z^*$ and all five final counts converge **jointly** after finite-economy centring:
--   $$n^{-1/2}\bigl(\boldsymbol\clubsuit_n(\tau_n^*)-n\boldsymbol f^{(n)}(\widehat z_n)\bigr)\Rightarrow N_5\!\left(0,J C(z^*)J^{\mathsf T}\right),$$
--   where the coordinates are $S,D,H^+,I^+,W$, $C(y)$ is the explicit corrected per-bank covariance, and $J=I-\alpha^{-1}\boldsymbol f'(z^*)e_W^{\mathsf T}$. For every $x\in X$ and $0\le\ell<\theta\le d_x^+$, the similarly centred final solvent count $S_{x,\theta,\ell}^{(n)}$ converges to a centred one-dimensional Gaussian with the explicit variance of $Z_{x,\theta,\ell}(t^*)-\alpha^{-1}s'_{x,\theta,\ell}(z^*)Z_W(t^*)$.
--
--   This is Theorem 3.7's final-size law, including both regimes, convergence of $\widehat z_n$, joint convergence in (8), and the class-specific limit (9).
--
--   **Formalization Note** The threshold support, threshold-lifetime independence and finite degree-sum equality are explicit. The finite $I^+$ and $W$ functions use $\lambda^{(n)}$. The printed covariance formulas (24) and (39) contain a factor $1/2$ in lifetime terms: for $d^+=1$, (24) gives $\mu q(y-y^2)/2$ where the actual Bernoulli variance is $\mu q y(1-y)$. The Gaussian covariance here is the corrected closed form. All counts are evaluated at the random $\tau_n^*$, including when $z^*=1$.
-- source:
--   Amini, Cao & Sulem, arXiv:2104.00248v1, p. 13, Theorem 3.7, equations (8)–(9); corrected covariance to pp. 31, 39, equations (24), (39)

import Mathlib
import Definitions.Def_DefaultContagion_FinalSize_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DefaultContagion.FinalSize

/-- Theorem 3.7, p. 13, with the corrected explicit covariance. -/
theorem theorem_3_7 {X : Type*} [Countable X] [DecidableEq X]
    (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (qn : ℕ → X → ℕ → ℝ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (h2 : Assumption2 dp typ qn mu q)
    (h3a : Assumption3a dp dm typ mu)
    (h3b : Assumption3b dp dm typ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : (n : ℕ) → Fin n → Ω → ℕ)
    (T : (n : ℕ) → Fin n → ℕ → Ω → ℝ)
    (hP : IsDeathProcess P dp typ qn Θ T) :
    let lam : ℝ := ∑' x, mu x * (dp x : ℝ)
    let zStar := lastZero (fW dp dm lam mu q)
    let zHat : ℕ → ℝ := fun n =>
      lastZero (fW dp dm (lamN dp typ n) (muN typ n) (qn n))
    let τ := tauStar dp dm typ Θ T
    let α := deriv (fW dp dm lam mu q) zStar
    (zStar = 0 → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => P {ω | ε ≤
        |stateVec dp dm typ Θ T n (τ n ω) ω 1 / n - 1|})
        atTop (𝓝 0)) ∧
    (0 < zStar → zStar ≤ 1 → 0 < α →
      Tendsto zHat atTop (𝓝 zStar) ∧
      TendstoInDistribution
        (fun n ω => (EuclideanSpace.equiv (Fin 5) ℝ).symm fun c =>
          (stateVec dp dm typ Θ T n (τ n ω) ω c -
            n * fVec dp dm (lamN dp typ n) (muN typ n) (qn n) (zHat n) c) /
            Real.sqrt n)
        atTop id (fun _ => P)
        (multivariateGaussian 0
          ((jac dp dm lam mu q zStar * covMat dp dm mu q zStar) *
            (jac dp dm lam mu q zStar).transpose)) ∧
      ∀ x θ l, l < θ → θ ≤ dp x →
        TendstoInDistribution
          (fun n ω => (Sxtl dp typ Θ T n x θ l (τ n ω) ω -
            n * sFun dp (muN typ n) (qn n) x θ l (zHat n)) / Real.sqrt n)
          atTop id (fun _ => P)
          (gaussianReal 0 (var9 dp dm lam mu q zStar x θ l).toNNReal)) := by sorry

end DefaultContagion.FinalSize
