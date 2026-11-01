-- Prove2me | Theorems.Thm_DevContest_phase_1_ic
-- name    : DevContest.phase_1_ic
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:55:05.198259+00:00
-- url     : https://prove2.me/theorems/e96a8e49-c3ed-48ee-915c-a31e758ace91
-- title:
--   Phase 1 of PCSD, p.ec18 — full effort is optimal throughout, with strict slack in the silent phase
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. Let $V_{0,t}$ be the value of the problem (EC.39) under PCSD from $t\ge0$, with the rival at full effort and with $V_1=V^\phi_1$. Then full effort attains $V_{0,t}$ from every date, and
--   $$
--   V^\phi_{1,t}-V_{0,t}>\frac c\lambda\qquad\text{for }0\le t<\underline t.
--   $$
--   Thus the silent phase does not need the disclosure of partial progress: incentives are high enough early in the contest.
--
--   **Formalization Note** When $\underline p=0$ the silent phase is empty and the displayed clause has no instance, which agrees with the theorem. The first clause holds at all dates, and so also covers phase 2.
--
--   Differences from the source:
--   - encoding: stated for beliefs $p<\underline p$, by the argument of Proposition 5, step 1 → stated for dates $0\le t<\underline t$ together with the value of (EC.39); reason: the belief $\lambda t/(1+\lambda t)$ is strictly increasing in the date on the silent phase; the strict inequality is the one printed on p.22
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, p.ec18; p.22 (after Theorem 2); Proposition 5, step 1, pp.ec9–ec10

import Mathlib
import Definitions.Def_DevContest_leaderRace
import Definitions.Def_DevContest_firstStageObjective

namespace DevContest

/-- Phase 1 of PCSD, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author
manuscript, p.ec18 and p.22: let `V0` be the value of the first-stage problem (EC.39) under PCSD,
with the rival at full effort. Then full effort attains `V0` from every date, and throughout the
silent phase `V_{1,t} - V_{0,t} > c/λ`.

**Formalization Note.** When `p̲ = 0` the silent phase is empty, and the second clause has no
instance. -/
theorem phase_1_ic {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) {V0 : ℝ → ℝ}
    (hV0 : ∀ t, 0 ≤ t → IsLUB {v | ∃ x, IsEffort x ∧
      v = firstStageObjective lam c (fun τ => pcsdContinuation lam c Rbar τ.toNNReal)
        (pcsdBelief lam c Rbar) (fun _ => 1) (fun _ => 1) (phiStar lam c Rbar) x t} (V0 t)) :
    (∀ t, 0 ≤ t →
      firstStageObjective lam c (fun τ => pcsdContinuation lam c Rbar τ.toNNReal)
        (pcsdBelief lam c Rbar) (fun _ => 1) (fun _ => 1) (phiStar lam c Rbar) (fun _ => 1) t =
        V0 t) ∧
    ∀ t, 0 ≤ t → t < tLow lam c Rbar →
      c / lam < pcsdContinuation lam c Rbar t.toNNReal - V0 t := by sorry

end DevContest
