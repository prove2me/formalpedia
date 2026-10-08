-- Prove2me | Theorems.Thm_CohenLeeSongLP_StochCentralPath_potential_expected_decrease
-- name    : CohenLeeSongLP.StochCentralPath.potential_expected_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:42:33.173862+00:00
-- url     : https://prove2.me/theorems/43bbde64-b60a-4569-aece-f8e5303613a9
-- title:
--   Lemma 4.13 — expected decrease of the potential $\Phi_\lambda(\mu/t-1)$
-- statement:
--   Let $n\ge 10$, let $A\in\mathbb R^{d\times n}$ have full row rank, let $\lambda=40\log n$, $t^{\mathrm{new}}=(1-\frac{\epsilon}{3\sqrt n})t$, and let $\delta_\mu$ be the direction of line 11 of Main,
--   $$\delta_\mu=\Big(\frac{t^{\mathrm{new}}}{t}-1\Big)xs-\frac{\epsilon}{2}\,t^{\mathrm{new}}\,\frac{\nabla\Phi_\lambda(\mu/t-1)}{\|\nabla\Phi_\lambda(\mu/t-1)\|_2}\qquad(\mu=xs).$$
--   Under Assumption 4.1 (with $0<\epsilon\le1/(40000\log n)$), the law of the sample accepted by StochasticStep is a probability measure and
--   $$\mathbf{E}\left[\Phi_\lambda\left(\frac{\mu^{\mathrm{new}}}{t^{\mathrm{new}}} - 1\right)\right] \le \Phi_\lambda\left(\frac{\mu}{t} - 1\right) - \frac{\lambda\epsilon}{15\sqrt{n}}\left(\Phi_\lambda\left(\frac{\mu}{t} - 1\right) - 10n\right).$$
--
--   The potential therefore decreases in expectation whenever it exceeds $10n$; iterated, this keeps $\mathbf E[\Phi]\le 10n$ along the whole run of Main (Lemma 4.14).
--
--   **Formalization Note** The choices $\lambda=40\log n$, $t^{\mathrm{new}}=(1-\epsilon/(3\sqrt n))t$ and the line-11 direction are fixed by Main and used in the paper's proof; they are hypotheses here. When $\nabla\Phi_\lambda(\mu/t-1)=0$ the second term of $\delta_\mu$ is taken to be $0$. No hypothesis $k\le n$ is imposed.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:18, Lemma 4.13 (proof pp. 3:18–3:20); p. 3:10, Algorithm 2, lines 3, 9, 11

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Main

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath

/-- Lemma 4.13 (p. 3:18): with `λ = 40 log n`, `t^new = (1 − ε/(3√n)) t` and `δ_μ` the direction
of line 11 of Main, under Assumption 4.1 the accepted step satisfies
`E[Φ_λ(μ^new/t^new − 1)] ≤ Φ_λ(μ/t − 1) − (λε/(15√n)) (Φ_λ(μ/t − 1) − 10n)`,
the expectation being over the conditioned law of StochasticStep (a probability measure). -/
theorem potential_expected_decrease {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : A.rank = d) (x s v : Fin n → ℝ) (t kSamp ε εmp : ℝ)
    (hAs : Assumption41 x s t v
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s) kSamp ε εmp) :
    IsProbabilityMeasure (stepLaw A x s v kSamp
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s)) ∧
    ∫ δ, potential (lam n)
        (fun i => muNew A x s v δ i / ((1 - ε / (3 * Real.sqrt n)) * t) - 1)
        ∂(stepLaw A x s v kSamp (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s))
      ≤ potential (lam n) (fun i => x i * s i / t - 1) -
        lam n * ε / (15 * Real.sqrt n) *
          (potential (lam n) (fun i => x i * s i / t - 1) - 10 * n) := by sorry

end CohenLeeSongLP.StochCentralPath
