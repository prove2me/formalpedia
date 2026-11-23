-- Prove2me | Theorems.Thm_CalibeatBandit_Supplement_bernstein_abs_tail
-- name    : CalibeatBandit.Supplement.bernstein_abs_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T19:00:57.150974+00:00
-- url     : https://prove2.me/theorems/8b846b03-f823-4bcf-8193-1fabe8f10ee5
-- title:
--   Freedman–Bernstein tail for martingales — $P(|\sum_{t<s}d_t|>\sqrt{2svL}+bL/3)\le2e^{-L}$
-- statement:
--   **Bernstein's inequality for martingales (two-sided).** Let $(\Omega,P)$ be a probability space with an increasing family of $\sigma$-algebras $\mathcal F_0\subseteq\dots\subseteq\mathcal F_s$, $s\ge1$. Let $d_0,\dots,d_{s-1}$ be random variables such that $d_t$ is $\mathcal F_{t+1}$-measurable and, for constants $b\ge0$ and $v>0$,
--
--   $$|d_t|\le b,\qquad\mathbb E[d_t\mid\mathcal F_t]=0,\qquad\mathbb E[d_t^2\mid\mathcal F_t]\le v\quad\text{almost surely}.$$
--
--   Then for every $L>0$,
--
--   $$P\Big(\Big|\sum_{t<s}d_t\Big|>\sqrt{2svL}+\frac{bL}3\Big)\ \le\ 2e^{-L}.$$
--
--   **Role.** This is the form of Freedman's inequality with a deterministic bound $v$ on the conditional variances: a sum of $s$ bounded martingale differences deviates by more than $\sqrt{2svL}+bL/3$ with probability at most $2e^{-L}$. In the proof of Theorem 3.5 it is applied, with $L$ of order $K\log K+\log(sT)$ and a union bound over swaps and rounds, to the difference between the estimated and the true swap regret of the recommendation, where $b=KT^\zeta+1$ and $v=KT^\zeta+2$. It gives the thresholds $C_s$ of Algorithm 2 their form.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Appendix C.4, proof of Theorem 3.5, p. 37 (the application of Freedman's inequality to the martingale differences $X_{t,\sigma}$). Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.Supplement.theorem_3_5.

import Mathlib

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal

theorem CalibeatBandit.Supplement.bernstein_abs_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) {s : ℕ} (hs : 0 < s)
    (hinfo : ∀ a n, a ≤ n → n ≤ s → info a ≤ info n)
    (hinfo_le : ∀ n ≤ s, info n ≤ mΩ)
    (d : ℕ → Ω → ℝ) {b v L : ℝ} (hb₀ : 0 ≤ b) (hv : 0 < v) (hL : 0 < L)
    (hm : ∀ t < s, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < s, ∀ ω, |d t ω| ≤ b)
    (hc : ∀ t < s, condExp (info t) P (d t) =ᵐ[P] 0)
    (hvX : ∀ t < s, condExp (info t) P (fun ω => d t ω ^ 2) ≤ᵐ[P] fun _ => v) :
    P {ω | Real.sqrt (2 * s * v * L) + b * L / 3 < |∑ t ∈ Finset.range s, d t ω|}
      ≤ 2 * ENNReal.ofReal (Real.exp (-L)) := by sorry
