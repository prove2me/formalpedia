-- Prove2me | Theorems.Thm_FixedMachinePrec_bucket_pass_closed
-- name    : FixedMachinePrec.bucket_pass_closed
-- status  : Open
-- author  : @kj
-- created : 2026-11-26T12:23:55.301221+00:00
-- url     : https://prove2.me/theorems/68468450-9113-41ac-9c3e-cc80a31804ec
-- title:
--   Initial records and edge closure after the bucket pass
-- statement:
--   For the records built for one parent, the final marked set contains each initial record and is closed under traversing a successful edge. The positive cardinality of every marked slot puts the source of an edge in an earlier prefix-size bucket than its target.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Lemma 5.5, p. 14 and Algorithm 4, p. 9.

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily

namespace FixedMachinePrec

theorem bucket_pass_closed {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (C : Finset (Finset (Fin N))) (W : Finset (Fin N)) (lk : Finset (Fin N) → Bool) : let st := buildStates prec m C W; let marked := (reachPass st lk).1; (∀ i a, st[i]? = some a → lk a.L = true → marked i = true) ∧ (∀ i j, marked i = true → edge st lk i j = true → marked j = true) := by sorry

end FixedMachinePrec
