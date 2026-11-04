-- Prove2me | Theorems.Thm_AIMInventory_Known_proposition_4_i
-- name    : AIMInventory.Known.proposition_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:29:33.593212+00:00
-- url     : https://prove2.me/theorems/16c8d1f4-e9ee-4061-a547-6bb302b5a50d
-- title:
--   Proposition 4 (i), corrected — E[|J_1(θ)|²] ≤ 1 + (21π²/2) E[(D−ED)⁶]/(ED − θ)⁶
-- statement:
--   Let $D_1, D_2, \dots$ be i.i.d. nonnegative demands with mean $E[D_1]$, let $0 < \theta < E[D_1]$, and suppose $E[D_1^6] < \infty$. Let $J_1(\theta)$ be the first busy period of Lindley's waiting-time process $W_1(\theta) = 0$, $W_{t+1}(\theta) = [W_t(\theta) + \theta - D_t]^+$. Then
--   $$E\big[|J_1(\theta)|^2\big] \le 1 + \frac{21\pi^2}{2}\cdot\frac{E\big[(D_1 - E[D_1])^6\big]}{(E[D_1]-\theta)^6}.$$
--
--   The paper prints the bound
--   $$E\big[|J_1(\theta)|^2\big] \le 7\pi^2\,\frac{E\big[(D_1 - E[D_1])^6\big]}{(E[D_1]-\theta)^6},$$
--   which is false: for deterministic demand $D_t \equiv d > \theta$ the queue empties after one period, $|J_1(\theta)| = 1$, and the printed right side is $0$. The printed proof bounds $P\{|J_1(\theta)| \ge \ell\}$ by a sum of $\ell$ terms where $\ell - 1$ are correct, which loses the term $P\{|J_1(\theta)| \ge 1\} = 1$. The statement above is the bound that the paper's argument (Markov's inequality and Lemma 12) gives after that correction.
--
--   The corollary for Theorem 2: the second moment of a busy period is finite, so the constant $C$ of the non-perishable case is finite.
--
--   **Formalization Note** The left side is a lower Lebesgue integral in $[0,\infty]$, with $|J_1(\theta)| = +\infty$ allowed. $E[D_1^6] < \infty$ is integrability of $D_1^6$. Indexing as in the mission's queue definitions ($W_1 = 0$, $\tau_0 = 1$, $|J_1(\theta)| = \tau_1(\theta) - 1$). Part (ii) of Proposition 4 is not stated (it is not used for Theorem 2 and fails on the same example).
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 9, Proposition 4 (i) (proof in Appendix B, p. 18); corrected constant

import Mathlib
import Definitions.Def_AIMInventory_Known_Queue
open MeasureTheory
open scoped ENNReal NNReal

namespace AIMInventory.Known

/-- Proposition 4 (i), p. 9, **corrected**: if `0 < θ < E[D_1]` and `E[D_1^6] < ∞`, then
`E[|J_1(θ)|²] ≤ 1 + (21π²/2) E[(D_1 − E[D_1])^6] / (E[D_1] − θ)^6`. The printed bound
`7π² E[(D_1 − E[D_1])^6] / (E[D_1] − θ)^6` fails for deterministic demand `D ≡ d > θ`, where
`|J_1(θ)| = 1` and the printed right side is `0`. -/
theorem proposition_4_i (P : CappedBaseStock.DemandLaw) (θ : ℝ) (hθ : 0 < θ)
    (hθlt : θ < CappedBaseStock.mean P)
    (h6 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 6) P.law) :
    ∫⁻ d, (busyLength θ d 1 : ℝ≥0∞) ^ 2 ∂(CappedBaseStock.demandPathLaw P)
      ≤ 1 + ENNReal.ofReal (21 * Real.pi ^ 2 / 2 *
          (∫ x : ℝ≥0, ((x : ℝ) - CappedBaseStock.mean P) ^ 6 ∂P.law) /
            (CappedBaseStock.mean P - θ) ^ 6) := by sorry

end AIMInventory.Known
