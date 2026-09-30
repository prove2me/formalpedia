-- Prove2me | Theorems.Thm_AlgMechDesign_MinWork_minwork_n_approx
-- name    : AlgMechDesign.MinWork.minwork_n_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:26:00.301811+00:00
-- url     : https://prove2.me/theorems/7be75b09-5b0a-4f3f-97a8-f592d1773cdb
-- title:
--   Claim 4.3 — MinWork is an n-approximation
-- statement:
--   Let $n \ge 1$ and let $x(\cdot)$ be any MinWork allocation rule. For every positive type vector $t$ and every allocation $y$,
--   $$
--   g(x(t), t) \le n \cdot g(y, t),
--   $$
--   that is, MinWork is an $n$-approximation for the minimal make-span, whatever the tie-breaking rule.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 177, Claim 4.3

import Mathlib
import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

namespace AlgMechDesign.MinWork

/-- Claim 4.3: for every tie-breaking rule, the MinWork allocation is an `n`-approximation of
the minimal make-span on positive types. -/
theorem minwork_n_approx {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc) :
    IsApprox (n : ℝ) alloc := by sorry

end AlgMechDesign.MinWork
