-- Prove2me | Theorems.Thm_A166944Research_band_exit_gap_le_half_record
-- name    : A166944Research.band_exit_gap_le_half_record
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-15T03:07:57.684144+00:00
-- url     : https://prove2.me/theorems/5f4cf19d-5fa4-4b5b-b2ba-be6b93deb364
-- title:
--   An A166944 replay that leaves the capped band does so with a gap of at most half the record
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944, $d_n = a_n - a_{n-1}$ its first differences and $D_n = a_n - n$ its offset from the identity. A **moving-horizon state** is a pair $(s,C)$ with $D_s = C$ and $s < C$; the recursion is quiet between states, and a **step** $(s,C) \to (r,C')$ records the first index $r > s$ at which the increment is nontrivial. Write
--
--   $$\mathrm{room}(s,C) \;=\; C - s$$
--
--   for how much horizon is left above the index, and call the **capped band** the set of states with $\mathrm{room} \le M$, where $M$ is the record from which the replay started.
--
--   The theorem concerns a step that **leaves** the band: the state is inside, $C - s \le M$, and the next state is outside, $M < C' - r$. For such a step,
--
--   $$2\,(r - s) + 1 \;\le\; M .$$
--
--   In words: **an exit from the band is a gain of room, and therefore a short step.** The gap is at most half the record.
--
--   This is not a curiosity. It says that a replay which leaves the band can come back — as one does from the record $M = 43$, visiting rooms $42$, then $45 > 43$, then $40$ — and the reason is structural rather than accidental: leaving *is* the mechanism by which the room grows. Consequently the tail of a replay cannot be packaged as a single in-band suffix unless the excursion is bounded separately.
--
--   The proof has two ingredients. The first is a one-step inequality containing no gap term, so that it composes along a path:
--
--   $$2\,d_r \;\le\; (C' - r) + 2 ,$$
--
--   which is equivalent to $(r-s) + d_r \le (C-s) + 1$. The second is that an exit has $\mathrm{room}$ strictly increasing, hence $d_r \ge (r-s) + 2$; substituting into the first gives the statement.
--
--   **Formalization Note** The hypothesis `C - s ≤ M` is stated on the room rather than as `s < C ∧ C - s ≤ M` because `IsMovingHorizonStep` already carries the state conditions; `hout` is the strict inequality that makes the step an exit rather than a boundary case. The constant `2` in `2 * (r - s) + 1 ≤ M` is optimal for the method: a stronger form `2*(r-s)+3 ≤ M` holds in every measured case but is not proved.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (conjecture of V. Shevelev, 2009). The moving-horizon formulation and this theorem are machine-checked at https://github.com/tara-sooo/A166944-Lean (A166944/BandExcursion.lean, A166944/BandReentry.lean).

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem band_exit_gap_le_half_record {s C r C' M : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hcap : C - s ≤ M) (hout : M < C' - r) :
    2 * (r - s) + 1 ≤ M := by
  sorry

end A166944Research
