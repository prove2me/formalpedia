-- Prove2me | Theorems.Thm_Bl_general_b_fact_second_bis_goal1
-- name    : Bl.general_b_fact_second_bis.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:45.884985+00:00
-- url     : https://prove2.me/theorems/cce40482-0db6-49c1-b97c-68584c02d0ed
-- title:
--   general b fact second bis: goal1
-- statement:
--   The general b fact second bis construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondBis/Imports.lean#L7-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondBis/Imports.lean#L7-L47

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second_bis

theorem Bl.general_b_fact_second_bis.goal1 :
  ∀ {g : Nat} [hg : Fact (Nat.Prime g)] (c : Formalism.CyclotomicNorms.Fbar g),
  Eq.{1} (HPow.hPow.{0, 0, 0} c g) c →
    Membership.mem.{0, 0}
      (Set.range.{0, 1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))) c := by sorry
