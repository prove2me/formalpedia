-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_stack_simulation
-- name    : EdgeSublinearMWIS.Main.stack_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:41:47.763197+00:00
-- url     : https://prove2.me/theorems/c9772ca6-0dfc-48a1-b62f-f8127cf4b280
-- title:
--   Polynomial simulation by an ordinary sequential bit machine
-- statement:
--   There is a universal positive integer exponent $q$ such that every fixed finite multi-stack program $P$ admits one finite sequential bit Turing machine $M$ and a fixed multiplier $K>0$. For every binary input $x$, output $z$, and step bound $t$, an actual halting execution of $P$ implies a first halting execution of $M$ with the same output in time
--   $$T_M(x)\le K(t+|x|+1)^q.$$
--   The simulator has no oracle, advice, catalyst string or assigned clock. The exponent precedes the simulated program. This supporting implementation target makes the algorithmic substrate compatible with the ordinary bit complexity used in Theorem 2; no simulation property is assumed by a definition or the goal.
--
--   Differences from the source:
--   - encoding: ordinary deterministic bit complexity → an explicit uniform polynomial simulation obligation between the two referenced finite machine models; reason: finite-stack arithmetic routines must be implemented by real local tape operations; the simulation overhead is proved, not granted
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Theorem 2 explanatory paragraph and §5.3 computational-model convention, p.2 (PDF p.2), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution

namespace EdgeSublinearMWIS.Main

/-- Polynomial simulation of the finite multi-stack model by the sequential bit model.
This is a supporting obligation, not an assumed free simulation. -/
theorem stack_simulation :
    ∃ q : ℕ, 0 < q ∧ ∀ P : Program,
      ∃ (M : CatalyticMatching.General.Machine) (K : ℕ), 0 < K ∧
        ∀ (input output : List Bool) (t : ℕ), Runs P input output t →
          ∃ s : ℕ, BitHalts M input output s ∧ s ≤ K * (t + input.length + 1) ^ q := by sorry

end EdgeSublinearMWIS.Main
