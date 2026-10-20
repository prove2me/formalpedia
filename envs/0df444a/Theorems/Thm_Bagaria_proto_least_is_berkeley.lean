-- Prove2me | Theorems.Thm_Bagaria_proto_least_is_berkeley
-- name    : Bagaria.proto_least_is_berkeley
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T23:14:03.768155+00:00
-- url     : https://prove2.me/theorems/317301b5-4146-437a-8e8f-683da0c0818b
-- title:
--   The least proto-Berkeley cardinal is Berkeley
-- statement:
--   Theorem of slide 12: if δ₀ is the least proto-Berkeley cardinal in a universe satisfying ZF, then δ₀ is already a Berkeley cardinal: for every transitive set containing δ₀ and every η below δ₀ there is a non-trivial elementary self-embedding of the transitive set whose critical point lies strictly between η and δ₀.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, p. 12, Theorem

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley

universe v

namespace Bagaria

open Universe

/-- Theorem of slide 12: the least proto-Berkeley cardinal is Berkeley. If
δ0 is proto-Berkeley and no smaller ordinal is, then every transitive set
containing the code of δ0 and every η below δ0 admit a non-trivial
elementary self-embedding of the transitive set whose critical point lies
strictly between η and δ0. -/
theorem proto_least_is_berkeley (U : Universe.{v}) (hZF : SatisfiesZF U.mem)
    (δ0 : Ordinal.{v}) (hP : U.protoBerkeley δ0)
    (hL : ∀ δ : Ordinal.{v}, δ < δ0 → ¬ U.protoBerkeley δ) :
    U.berkeley δ0 := by
  sorry

end Bagaria
