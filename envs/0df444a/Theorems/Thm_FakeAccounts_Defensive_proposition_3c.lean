-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_proposition_3c
-- name    : FakeAccounts.Defensive.proposition_3c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:10.262261+00:00
-- url     : https://prove2.me/theorems/92e50874-2bff-45ef-b498-37176a63921e
-- title:
--   Proposition 3(c), p. 8875 — the defensive purchase falls in $d$ on $[0,d_2]$ iff (22); otherwise it rises then falls
-- statement:
--   Fix model parameters in the standing ranges with $c_0>0$, $p_0>0$, and Assumption 3: $p_0<\eta_2=\frac1l\lambda_i\mu(1-l^2)$. Let $d_2=(1-\tau)(\eta_2-p_0)$, so that $[0,d_2]$ is the range of antifake efforts that sustain the costly separating equilibrium, and let $x_H^{csep}(d)$ be the H-type's defensive purchase there. Consider condition (22):
--   $$c_1(1-\tau)^2\ \le\ \frac{\lambda_i\mu(1-l^2)\,c_0}{p_0\big[\lambda_i\mu(1-l^2)-p_0 l\big]} .$$
--
--   1. If (22) holds, $x_H^{csep}$ is strictly decreasing in $d$ on $[0,d_2]$.
--   2. If (22) fails, there is $\hat d$ with $0<\hat d<d_2$ such that $x_H^{csep}$ is strictly increasing on $[0,\hat d]$ and strictly decreasing on $[\hat d,d_2]$.
--
--   So a platform that raises its antifake effort can provoke *more* defensive purchases of fake accounts by high-quality influencers, unless the antifake technology is good enough for (22) to hold.
--
--   **Formalization Note.** "Decreases" is strict monotonicity; "first increases and then decreases" is the existence of an interior peak with strict monotonicity on each side. The statement is on $[0,d_2]$, the costly separating range when no pooling equilibrium exists; when pooling exists for small $d$ the costly separating range is $(d_1,d_2]$, a subinterval, on which part 1 still gives decrease, while the peak of part 2 may lie below $d_1$. Condition (22) is kept as the printed quotient; its denominator is positive under $p_0>0$ and Assumption 3. The hypotheses $c_0>0$ (a consumer's opportunity cost; with $c_0=0$ the purchase vanishes at $d=0$) and $p_0>0$ (a price; (22) divides by it) are added; Assumptions 1–2 are not imposed.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, Proposition 3(c), (22); Assumption 3, p. 8873

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- Proposition 3(c), p. 8875: under (22) x_H^csep strictly decreases on [0, d₂]; otherwise
it strictly increases on [0, d̂] and strictly decreases on [d̂, d₂] for some d̂ ∈ (0, d₂). -/
theorem proposition_3c (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) (hp0 : 0 < P.p0)
    (hA3 : P.p0 < FakeAccounts.Platform.eta2 P) :
    (P.c1 * (1 - P.tau) ^ 2 ≤ P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
        (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) →
      StrictAntiOn (xCsepH P) (Set.Icc 0 (FakeAccounts.Platform.d2 P))) ∧
    (P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
        (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) < P.c1 * (1 - P.tau) ^ 2 →
      ∃ dh, 0 < dh ∧ dh < FakeAccounts.Platform.d2 P ∧ StrictMonoOn (xCsepH P) (Set.Icc 0 dh) ∧
        StrictAntiOn (xCsepH P) (Set.Icc dh (FakeAccounts.Platform.d2 P))) := by sorry

end FakeAccounts.Defensive
