-- Prove2me | Theorems.Thm_Bagaria_no_extendible_below_least_berkeley
-- name    : Bagaria.no_extendible_below_least_berkeley
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T23:14:42.18498+00:00
-- url     : https://prove2.me/theorems/dc2b47a3-95e6-4207-839a-9a4c872305b3
-- title:
--   No extendible cardinal lies at or below the least Berkeley cardinal
-- statement:
--   Corollary of slide 13: if δ₀ is the least Berkeley cardinal in a universe satisfying ZF, then no extendible cardinal lies at or below δ₀. Being Berkeley is a Π₂ property, so no Σ₃-correct cardinal can lie at or below the first Berkeley cardinal; in particular extendibility fails there. The formalization captures the extendible corollary; the Σ₃-correctness clause is out of scope.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, p. 13; Kanamori (2003), The Higher Infinite, extendible cardinals

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley

universe v

namespace Bagaria

open Universe

/-- Corollary of slide 13: no extendible cardinal lies at or below the
least Berkeley cardinal. Being Berkeley is a Π₂ property of the universe,
so no Σ₃-correct cardinal lies at or below the least Berkeley cardinal; in
particular extendibility fails there. The formalization captures the
extendible corollary; the Σ₃-correctness clause is out of scope. -/
theorem no_extendible_below_least_berkeley (U : Universe.{v}) (hZF : SatisfiesZF U.mem)
    (δ0 : Ordinal.{v}) (hB : U.berkeley δ0)
    (hL : ∀ δ : Ordinal.{v}, δ < δ0 → ¬ U.berkeley δ) :
    ∀ κ : Ordinal.{v}, κ ≤ δ0 → ¬ U.isExtendible κ := by
  sorry

end Bagaria
