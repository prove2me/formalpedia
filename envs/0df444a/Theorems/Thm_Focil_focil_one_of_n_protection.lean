-- Prove2me | Theorems.Thm_Focil_focil_one_of_n_protection
-- name    : Focil.focil_one_of_n_protection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:38:19.051863+00:00
-- url     : https://prove2.me/theorems/f4e3e8d0-506f-45f9-9685-d1109e787aaf
-- title:
--   Focil: focil one of n protection
-- statement:
--   **FOCIL's 1-of-N censorship-resistance guarantee.**
--
--     This is the formal counterpart of EIP-7805's marquee claim:
--     it suffices that *at least one* non-equivocating IL committee
--     member listed the transaction for it to be force-included in
--     any canonical block (modulo invalidity and block fullness).
--
--     The witness IL is existentially quantified inside
--     `h_listed_by_some_honest_member`: the theorem fires whenever
--     the fork-choice store contains *some* non-equivocating IL
--     carrying `tx`. The other ILs in the store are irrelevant; an
--     adversary controlling some committee seats and equivocating
--     the rest does not defeat the guarantee, as long as at least
--     one seat publishes a non-equivocating IL containing `tx`.
--
--     Hypotheses:
--
--     - `h_listed_by_some_honest_member`:
--                            there exists a stored, non-equivocating
--                            IL `il` with `tx ∈ il.transactions`.
--     - `h_can_append`:      `tx` could be validly appended to `b`.
--     - `h_block_not_full`:  `b` does not satisfy `fc.full`.
--     - `h_canonical`:       `b` is the canonical chain head.
--
--     Conclusion: `tx ∈ b.transactions`.
--
--     Caveats:
--
--     - "Honest member" here means "not in the equivocator set,"
--       which captures the 1-of-N guarantee as the EIP states it.
--       A Byzantine member who has not yet been caught equivocating
--       still satisfies the precondition; the guarantee degrades to
--       "1-of-(N − equivocators)" once equivocators have been
--       detected. See FINDINGS.md §2.4 and `Tests/Examples.lean`
--       Scenarios 9–10 for concrete demonstrations.
--     - All caveats from `focil_censorship_resistance` apply.
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Safety.lean#L146-L160
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Safety.lean#L146-L160

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
set_option autoImplicit false
open Focil

theorem Focil.focil_one_of_n_protection
    (fc : ForkChoice) (b : Block) (tx : Transaction)
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ fc.state.stored_ils
            ∧ IsConsidered fc.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : fc.canAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by sorry
