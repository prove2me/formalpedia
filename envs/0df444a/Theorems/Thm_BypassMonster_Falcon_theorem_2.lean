-- Prove2me | Theorems.Thm_BypassMonster_Falcon_theorem_2
-- name    : BypassMonster.Falcon.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:29.098523+00:00
-- url     : https://prove2.me/theorems/474e4839-5d95-4f69-8955-83209367a8a3
-- title:
--   Theorem 2, p. 1914 (explicit form, p. 1928) — w.p. ≥ 1−δ, FALCON+ has regret ≤ 14.3 Σ_{m=2}^{m(T)} √(Kℰ_{ℱ,δ/(2m²)}(τₘ₋₁−τₘ₋₂))(τₘ−τₘ₋₁) + τ₁ + √(8T log(2/δ))
-- statement:
--   Consider the stochastic contextual bandit with $K$ actions, a finite context set and rewards in $[0,1]$, and an offline regression oracle satisfying Assumption 2 with error function $\mathcal E_{\mathcal F,\delta}(n)>0$. Run FALCON+ (Algorithm 2) with confidence parameter $\delta>0$, tuning parameter $c=1/2$, and an epoch schedule $0=\tau_0<\tau_1<\tau_2<\cdots$. Let $T\ge1$ and let $m(T)=\min\{m\ge1:T\le\tau_m\}$ be the number of epochs run in $T$ rounds. Assume $\tau_m\ge2^m$ for $1\le m\le m(T)$ and $\gamma_1\le\cdots\le\gamma_{m(T)}$. Then, with probability at least $1-\delta$, the regret of FALCON+ after $T$ rounds satisfies
--   $$\sum_{t=1}^T\big(r_t(\pi_{f^*}(x_t))-r_t(a_t)\big)\le 14.3\sum_{m=2}^{m(T)}\sqrt{K\,\mathcal E_{\mathcal F,\delta/(2m^2)}(\tau_{m-1}-\tau_{m-2})}\,(\tau_m-\tau_{m-1})+\tau_1+\sqrt{8T\log(2/\delta)}.$$
--
--   This is the paper's main result: a contextual bandit algorithm that calls an arbitrary offline regression oracle only $O(\log T)$ (or $O(\log\log T)$) times achieves regret governed by the oracle's estimation error, which for rate-optimal oracles is the minimax rate.
--
--   **Formalization Note** The page states Theorem 2 as $O\big(\sqrt K\sum_{m=2}^{m(T)}\sqrt{\mathcal E_{\mathcal F,\delta/(2m^2)}(\tau_{m-1}-\tau_{m-2})}(\tau_m-\tau_{m-1})\big)$; the statement here is the explicit bound its proof establishes (p. 1928), with the additive terms $\tau_1+\sqrt{8T\log(2/\delta)}$ kept. The proof's last step is printed "$=$"; it is an inequality (the last epoch is cut at $T$). The context set is finite, the setting of the paper's detailed proof (App. A.1–A.6); no constant depends on $|\mathcal X|$. Rewards lie in $[0,1]$, as the proof of Theorem 2 assumes. The run is realized on a canonical product space; "with probability at least $1-\delta$" is stated as "the failure set has outer measure at most $\delta$". Added hypotheses, all in `Setup2`: $\mathcal E>0$ (Algorithm 2 divides by it), measurability of the oracle and of the tie-breaking rule for the greedy action (App. A.7, p. 1929), and $\delta>0$. The policy $\pi_{f^*}$ is any maximizer of $f^*(x,\cdot)$.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Theorem 2 and Eq. (4), p. 1914; App. A.6, Proof of Theorem 2, p. 1928

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Theorem 2** (p. 1914), in the explicit form established by its proof (App. A.6, p. 1928):
under Setup 2 with `τ_m ≥ 2^m` and `γ_1 ≤ ⋯ ≤ γ_{m(T)}` for `m ≤ m(T)`, with probability at least
`1 − δ` the regret of FALCON+ after `T` rounds is at most
`14.3 ∑_{m=2}^{m(T)} √(K ℰ_{ℱ,δ/(2m²)}(τ_{m−1} − τ_{m−2})) (τ_m − τ_{m−1}) + τ_1 + √(8T log(2/δ))`.
Stated in failure form on the canonical space. -/
theorem theorem_2
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (T : ℕ) (hT : 1 ≤ T) (hS : Setup2 DX ν A πstar (epochOf A.τ T)) :
    canonMeasure DX ν {ω | 143 / 10 * ∑ m ∈ Finset.Icc 2 (epochOf A.τ T),
          Real.sqrt ((K : ℝ) * A.E (A.δ / (2 * (m : ℝ) ^ 2)) (A.τ (m - 1) - A.τ (m - 2)))
            * ((A.τ m - A.τ (m - 1) : ℕ) : ℝ)
        + (A.τ 1 : ℝ) + Real.sqrt (8 * (T : ℝ) * Real.log (2 / A.δ)) < A.regret πstar T ω}
      ≤ ENNReal.ofReal A.δ := by sorry

end BypassMonster.Falcon
