-- Prove2me | Theorems.Thm_ClawFreeChoosable_theorem_12_2_chudnovsky_seymour
-- name    : ClawFreeChoosable.theorem_12_2_chudnovsky_seymour
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:35.429623+00:00
-- url     : https://prove2.me/theorems/34927d6a-504e-40bb-83cb-570db4d23e19
-- title:
--   Theorem 12.2 (Chudnovsky–Seymour) — rich clique cutsets
-- statement:
--   A finite connected claw-free graph with a rich clique cutset is of interval type or admits a double clique cutset.
--
--   This structural theorem of Chudnovsky and Seymour ([CS04, Theorem 1.4]) is cited, not proved, in the paper; it is the step that removes rich clique cutsets from a minimum counterexample.
--
--   Differences from the source:
--   - encoding: connected graph → Mathlib's Connected, which includes nonemptiness; reason: the empty graph has no rich clique cutset, so no instance changes
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Theorem 12.2, p.33 (PDF p.36); also stated p.7 (PDF p.10); cited from [CS04, Theorem 1.4]

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsClawFree
import Definitions.Def_ClawFreeChoosable_IsRichCliqueCutset
import Definitions.Def_ClawFreeChoosable_IsIntervalType
import Definitions.Def_ClawFreeChoosable_HasDoubleCliqueCutset

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Theorem 12.2 (Chudnovsky–Seymour [CS04, Theorem 1.4])** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.33; also stated p.7): a
connected claw-free graph with a rich clique cutset is of interval type or admits a double
clique cutset.

**Formalization Note.** Cited in the paper, not proved there (M. Chudnovsky, P. Seymour, *A
structure theorem for claw-free perfect graphs*, manuscript, 2004 [CS04, Theorem 1.4]). Stated as printed, without a
"perfect" hypothesis, with this paper's definitions of rich clique cutsets (§12.1), interval
type (Definition 11.1) and double clique cutsets (§12.1). -/
theorem theorem_12_2_chudnovsky_seymour {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hclaw : IsClawFree G) (hrich : ∃ K : Set V, IsRichCliqueCutset G K) :
    IsIntervalType G ∨ HasDoubleCliqueCutset G := by sorry

end ClawFreeChoosable
