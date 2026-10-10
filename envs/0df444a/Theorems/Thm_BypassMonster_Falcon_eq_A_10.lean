-- Prove2me | Theorems.Thm_BypassMonster_Falcon_eq_A_10
-- name    : BypassMonster.Falcon.eq_A_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:28:02.434802+00:00
-- url     : https://prove2.me/theorems/c8826cf9-1b00-4e6c-8604-4068f834c5cd
-- title:
--   Display (A.10), p. 1927 — Azuma: Σ_{t=1}^T Mₜ ≤ 2√(2T log(2/δ)) w.p. ≥ 1−δ/2
-- statement:
--   Consider Setup 2 with rewards in $[0,1]$ and a number of rounds $T\ge1$. For each round $t$ let
--   $$M_t=r_t(\pi_{f^*}(x_t))-r_t(a_t)-\sum_{\pi\in\Psi}Q_{m(t)}(\pi)\,\mathrm{Reg}(\pi).$$
--   Then, with probability at least $1-\delta/2$,
--   $$\sum_{t=1}^T M_t\le 2\sqrt{2T\log(2/\delta)}.$$
--
--   The $M_t$ form a martingale difference sequence bounded by $2$ (Lemma A.4), and the display is Azuma's inequality for it; it converts the expected-regret analysis into a high-probability bound.
--
--   **Formalization Note** Stated in failure form: the set where $\sum_t M_t>2\sqrt{2T\log(2/\delta)}$ has outer measure at most $\delta/2$. For $\delta\ge2$ the logarithm is $\le 0$ and the claim holds trivially. Finite $\mathcal X$.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), proof of Lemma A.10, display (A.10), p. 1927

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Display (A.10)** (proof of Lemma A.10, p. 1927): with `[0,1]` rewards and
`M_t = r_t(π_{f*}(x_t)) − r_t(a_t) − ∑_{π ∈ Ψ} Q_{m(t)}(π) Reg(π)`, with probability at least `1 − δ/2`,
`∑_{t=1}^{T} M_t ≤ 2√(2T log(2/δ))`. Stated in failure form. -/
theorem eq_A_10
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (M : ℕ) (hS : Setup2 DX ν A πstar M) (T : ℕ) (hT : 1 ≤ T) :
    canonMeasure DX ν {ω | 2 * Real.sqrt (2 * (T : ℝ) * Real.log (2 / A.δ))
        < ∑ t ∈ Finset.Icc 1 T, A.Mt DX ν πstar t ω} ≤ ENNReal.ofReal (A.δ / 2) := by sorry

end BypassMonster.Falcon
