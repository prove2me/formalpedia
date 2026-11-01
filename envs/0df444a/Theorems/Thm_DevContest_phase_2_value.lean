-- Prove2me | Theorems.Thm_DevContest_phase_2_value
-- name    : DevContest.phase_2_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:54:55.809217+00:00
-- url     : https://prove2.me/theorems/b3d8929d-f18a-4ae0-a8f0-9ededb922321
-- title:
--   Phase 2 of PCSD, p.ec18 — a first success is worth exactly $c/\lambda$, and $V_0=0$
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. Then:
--
--   1. $V^\phi_{1,t}=c/\lambda$ at every date $t\ge\underline t$;
--   2. consequently, from every date $t\ge\underline t$ the objective (EC.39) under PCSD vanishes for every effort path, with the rival at full effort.
--
--   So $V^\phi_{0,t}=0$, and full effort is incentive compatible, at every $t\ge\underline t$: PCSD gives the bare minimum of surplus that keeps agents working.
--
--   Differences from the source:
--   - encoding: for any belief $p\ge\underline p$, and all $t\ge\underline t$ → at every date $t\ge\underline t$; reason: the belief is a strictly increasing function of the date from $\underline t$ on, and starts from $\underline p$
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, p.ec18

import Mathlib
import Definitions.Def_DevContest_leaderRace
import Definitions.Def_DevContest_firstStageObjective

open scoped NNReal

namespace DevContest

/-- Phase 2 of PCSD, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author
manuscript, p.ec18: `V^φ_{1,p} = c/λ` at every date from `t̲` on. Consequently the objective (EC.39)
vanishes for every effort from every such date, so `V^φ_{0,p} = 0` and full effort is incentive
compatible. -/
theorem phase_2_value {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) :
    (∀ t : ℝ≥0, tLow lam c Rbar ≤ t → pcsdContinuation lam c Rbar t = c / lam) ∧
    ∀ t, tLow lam c Rbar ≤ t → ∀ x, IsEffort x →
      firstStageObjective lam c (fun τ => pcsdContinuation lam c Rbar τ.toNNReal)
        (pcsdBelief lam c Rbar) (fun _ => 1) (fun _ => 1) (phiStar lam c Rbar) x t = 0 := by sorry

end DevContest
