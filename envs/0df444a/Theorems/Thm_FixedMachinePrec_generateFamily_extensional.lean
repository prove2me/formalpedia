-- Prove2me | Theorems.Thm_FixedMachinePrec_generateFamily_extensional
-- name    : FixedMachinePrec.generateFamily_extensional
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T12:23:45.646213+00:00
-- url     : https://prove2.me/theorems/01767872-fa62-4992-935a-5246228e049a
-- title:
--   Membership in a generated layer is bounded formula representability
-- statement:
--   For any rank function and decidable relation, Algorithm 1 generates exactly the valuations of admissible formulas with at most $k$ leaves, for every positive $k$. This is extensional: it does not assert that the output list has no repetitions.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Lemma 5.3, p. 13 and Algorithm 1, p. 5.

import Mathlib
import Definitions.Def_FixedMachinePrec_GenerateFamily

namespace FixedMachinePrec

theorem generateFamily_extensional {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (rank : Fin N → ℕ) (k : ℕ) (hk : 1 ≤ k) : (generateFamily prec rank m k).toFinset = family prec rank m k := by sorry

end FixedMachinePrec
