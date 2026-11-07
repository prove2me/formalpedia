-- Prove2me | Theorems.Thm_ClawFreeChoosable_theorem_1_2_chvatal_sbihi
-- name    : ClawFreeChoosable.theorem_1_2_chvatal_sbihi
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:48.034852+00:00
-- url     : https://prove2.me/theorems/797beb7c-2dd8-4a38-9e52-45385e61ff61
-- title:
--   Theorem 1.2 (Chvátal–Sbihi) — claw-free perfect atoms are elementary or peculiar
-- statement:
--   Every finite claw-free perfect atom is elementary or peculiar, where "peculiar" is taken in the standard nondegenerate sense: a peculiar partition (Definition 12.4) in which all nine cliques $A_i, B_i, K_i$ are nonempty.
--
--   This decomposition theorem of Chvátal and Sbihi ([CS88]) is cited, not proved, in the paper; it reduces the atoms of the proof of Theorem 1.3 to two classes.
--
--   Differences from the source:
--   - reading: peculiar (Definition 12.4 allows K1, K2, K3 to be empty and notes that the standard nondegenerate definition requires all nine cliques to be nonempty) → IsPeculiarStd: a peculiar partition with all nine cliques nonempty; reason: the theorem is cited from [CS88], whose definition is the nondegenerate one; this is the stronger of the two conclusions and implies peculiarity in the sense of Definition 12.4
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Theorem 1.2, p.1 (PDF p.4); cited from [CS88]; Definition 12.4, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_ClawFreeChoosable_IsClawFree
import Definitions.Def_ClawFreeChoosable_IsAtom
import Definitions.Def_ClawFreeChoosable_IsElementary
import Definitions.Def_ClawFreeChoosable_IsPeculiar

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Theorem 1.2 (Chvátal–Sbihi [CS88])** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.1): every claw-free perfect atom is
elementary or peculiar.

**Formalization Note.** Cited in the paper, not proved there (V. Chvátal, N. Sbihi, *Recognizing claw-free
perfect graphs*, J. Combin. Theory Ser. B 44 (1988) [CS88]). "Peculiar" in the conclusion is the
standard nondegenerate definition `IsPeculiarStd` (all nine cliques of Definition 12.4 nonempty,
as in [CS88]); this is the stronger of the two readings, and implies peculiarity in the sense of
Definition 12.4. -/
theorem theorem_1_2_chvatal_sbihi {V : Type} [Fintype V] (G : SimpleGraph V)
    (hclaw : IsClawFree G) (hperf : StrongPerfectGraph.Main.IsPerfect G) (hatom : IsAtom G) :
    IsElementary G ∨ IsPeculiarStd G := by sorry

end ClawFreeChoosable
