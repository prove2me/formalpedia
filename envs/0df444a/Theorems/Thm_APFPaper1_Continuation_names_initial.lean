-- Prove2me | Theorems.Thm_APFPaper1_Continuation_names_initial
-- name    : APFPaper1.Continuation.names_initial
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:50:28.146463+00:00
-- url     : https://prove2.me/theorems/06c71eec-3ec8-466f-9403-435c6a2e441e
-- title:
--   A concatenation’s initial word names an initial process
-- statement:
--   If a concatenation names q, there exists a process p named by its first word such that p is an initial segment of q. The suffix is exactly the second word; no admissibility claim about the prefix is made. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_naming.lean, declaration at line 43 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.names_initial {g h k : Context} (word : Word Frag g h) (v : Word Frag h k)
    (q : WordFrom Frag g) (hq : names (word.append v) q) :
    ∃ p : WordFrom Frag g, names word p ∧ IsPrefix p q := by sorry
