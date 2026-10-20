-- Prove2me | Theorems.Thm_Bagaria_berkeley_reflects_reinhardt
-- name    : Bagaria.berkeley_reflects_reinhardt
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T23:16:13.428063+00:00
-- url     : https://prove2.me/theorems/275ed984-84b2-49ba-abaf-79073c1fc549
-- title:
--   The least Berkeley cardinal rank-reflects a Reinhardt cardinal
-- statement:
--   Theorem of slide 14, Reinhardt half: if δ₀ is the least Berkeley cardinal in a universe satisfying ZF, then some ordinal γ below δ₀ carries a rank segment that satisfies ZF and contains a Reinhardt cardinal. The source moreover obtains an ω-huge cardinal above κ_ω(j); that clause is not formalized here.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, p. 14, Theorem (Reinhardt half)

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley

universe v

namespace Bagaria

open Universe

/-- Theorem of slide 14, Reinhardt half: the least Berkeley cardinal
strongly rank-reflects a Reinhardt cardinal. If δ0 is the least Berkeley
cardinal, then some ordinal γ below δ0 carries a rank segment that
satisfies ZF and contains a Reinhardt cardinal. The source obtains the
conclusion together with an ω-huge cardinal above κ_ω(j); that clause is
not formalized here. -/
theorem berkeley_reflects_reinhardt (U : Universe.{v}) (hZF : SatisfiesZF U.mem)
    (δ0 : Ordinal.{v}) (hB : U.berkeley δ0)
    (hL : ∀ δ : Ordinal.{v}, δ < δ0 → ¬ U.berkeley δ) :
    ∃ γ : Ordinal.{v}, γ < δ0 ∧ SatisfiesZF (U.segmentMem γ) ∧ U.hasReinhardtIn γ := by
  sorry

end Bagaria
