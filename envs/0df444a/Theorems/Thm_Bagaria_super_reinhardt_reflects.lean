-- Prove2me | Theorems.Thm_Bagaria_super_reinhardt_reflects
-- name    : Bagaria.super_reinhardt_reflects
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T23:13:19.776366+00:00
-- url     : https://prove2.me/theorems/7d27a1e7-ba50-4151-9c5a-092f287ee92b
-- title:
--   A super Reinhardt cardinal strongly rank-reflects a Reinhardt cardinal
-- statement:
--   Theorem of slide 11: if κ is a super Reinhardt cardinal in a universe satisfying ZF, then some ordinal γ below κ carries a rank segment that itself satisfies ZF and contains a Reinhardt cardinal. The consistency strength chain CON(totally Reinhardt) implies CON(super Reinhardt) implies CON(Reinhardt) is read off from such reflection statements.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, p. 11, Theorem

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley

universe v

namespace Bagaria

open Universe

/-- Theorem of slide 11: a super Reinhardt cardinal strongly rank-reflects
a Reinhardt cardinal. If κ is super Reinhardt, then some ordinal γ below κ
carries a rank segment that satisfies ZF and contains a Reinhardt
cardinal — the first-order approximation of ⟨V_γ, V_{γ+1}⟩ satisfying ZF₂
together with "There exists a Reinhardt cardinal". -/
theorem super_reinhardt_reflects (U : Universe.{v}) (hZF : SatisfiesZF U.mem)
    (κ : Ordinal.{v}) (h : U.isSuperReinhardt κ) :
    ∃ γ : Ordinal.{v}, γ < κ ∧ SatisfiesZF (U.segmentMem γ) ∧ U.hasReinhardtIn γ := by
  sorry

end Bagaria
