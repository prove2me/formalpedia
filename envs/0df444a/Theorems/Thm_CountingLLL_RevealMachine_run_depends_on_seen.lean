-- Prove2me | Theorems.Thm_CountingLLL_RevealMachine_run_depends_on_seen
-- name    : CountingLLL.RevealMachine.run_depends_on_seen
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:46:13.316816+00:00
-- url     : https://prove2.me/theorems/b813e58d-f096-4091-a813-a835ad7aadb2
-- title:
--   Finite machine execution depends only on the coordinates read
-- statement:
--   For a deterministic machine that reads at most one array coordinate per step, suppose two input arrays agree on every coordinate read by the first execution during its first $n$ steps. Then the two executions have identical program states and identical sets of read coordinates after those steps.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_RevealMachine
open CountingLLL.RevealMachine

theorem CountingLLL.RevealMachine.run_depends_on_seen {σ ι α : Type*} [DecidableEq ι] (P : Program σ ι α)
    (ω ω' : ι → α) (initial : σ) (n : ℕ)
    (h : ∀ i ∈ (run P ω initial n).2, ω i = ω' i) :
    run P ω initial n = run P ω' initial n := by sorry
