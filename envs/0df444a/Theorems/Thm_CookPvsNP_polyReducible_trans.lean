-- Prove2me | Theorems.Thm_CookPvsNP_polyReducible_trans
-- name    : CookPvsNP.polyReducible_trans
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T06:26:32.050686+00:00
-- url     : https://prove2.me/theorems/ba6139c4-bd0f-4309-b801-c0616888efa6
-- title:
--   Cook, Definition 3 — polynomial-time many-one reducibility is transitive
-- statement:
--   If L₁ is polynomial-time many-one reducible to L₂ and L₂ is polynomial-time many-one reducible to L₃, then L₁ is polynomial-time many-one reducible to L₃. Together with the closure of polynomial-time computable functions under composition, this is the standard transitivity of Cook’s ≤ₚ. It is the step that lets the NP-hardness of a source problem be transferred through a target problem by composing the two reductions, rather than requiring the composition to be carried out once and for all by hand.
-- source:
--   Cook, The P versus NP problem, Clay Mathematics Institute (2000), §1 p. 2 and Definition 3 p. 2

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- Polynomial-time many-one reducibility is transitive. -/
theorem polyReducible_trans {Sym₁ Sym₂ Sym₃ : Type} {L₁ : Lang Sym₁}
    {L₂ : Lang Sym₂} {L₃ : Lang Sym₃} (h₁₂ : PolyReducible L₁ L₂)
    (h₂₃ : PolyReducible L₂ L₃) : PolyReducible L₁ L₃ := by
  sorry

end CookPvsNP
