-- Prove2me | Theorems.Thm_AcquihiringMonopsony_PrivateInfo_monopsony_wage_zero
-- name    : AcquihiringMonopsony.PrivateInfo.monopsony_wage_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:53.078339+00:00
-- url     : https://prove2.me/theorems/ab60a24d-6dd0-49cc-9f3b-270f1dd15cc2
-- title:
--   §6, p. 15 — a monopsonist pays wage 0: the startup earns v_s, the acquirer v_a
-- statement:
--   Consider the private-benefit model of §6: the employee's benefit at the startup is $b \sim U[0,B]$, her outside option is worth $0$, and $0 < B < \min\{v_a,v_s\}$, $v_s - B < v_a < v_s + 2B$.
--
--   Suppose the startup is a monopsonist and offers wage $y$. A type-$b$ employee stays exactly when $y + b \ge 0$, so the startup's expected profit is
--   $$\Pi_s(y) = \frac1B\int_0^B (v_s - y)\,\mathbf 1\{y+b \ge 0\}\,db .$$
--   Then:
--
--   1. for every $c \in [0,B]$, the wage $-c$ (hiring only types with benefit at least $c$) yields $\Pi_s(-c) = (v_s + c)(B-c)/B$;
--   2. $\Pi_s(0) = v_s$;
--   3. every wage $y \neq 0$ yields $\Pi_s(y) < v_s$, so $0$ is the unique optimal wage.
--
--   Likewise, a monopsonistic acquirer offering wage $x$ (the employee has no benefit at the acquirer and accepts iff $x \ge 0$) earns $v_a$ at $x = 0$ and strictly less at every $x \ne 0$.
--
--   This is what makes Lemma 2 of the paper apply to acquihiring with wage floor $0$: the startup's stand-alone profit is $v_s$, the price an acquisition must beat, and after the acquisition the employee is paid $0$.
--
--   **Formalization Note** The optimization ranges over all real wages, not only the page's $[-B, 0]$; uniqueness of the maximizer is the page's "it follows that the startup would set a wage of $w_s = 0$".
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 15 (PDF 16), §6, fifth paragraph

import Mathlib
import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

namespace AcquihiringMonopsony.PrivateInfo

theorem monopsony_wage_zero (P : Params) (hP : P.Standing) :
    (∀ c ∈ Set.Icc (0:ℝ) P.B, monoProfitS P (-c) = (P.vs + c) * (P.B - c) / P.B) ∧
    monoProfitS P 0 = P.vs ∧ (∀ y : ℝ, y ≠ 0 → monoProfitS P y < P.vs) ∧
    monoProfitA P 0 = P.va ∧ (∀ x : ℝ, x ≠ 0 → monoProfitA P x < P.va) := by sorry

end AcquihiringMonopsony.PrivateInfo
