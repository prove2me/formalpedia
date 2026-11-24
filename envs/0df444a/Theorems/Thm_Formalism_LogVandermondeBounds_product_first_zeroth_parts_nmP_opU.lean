-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmP_opU
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP_opU
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:36.003811+00:00
-- url     : https://prove2.me/theorems/13b2fec3-2aa9-47e0-aeac-c601f33aa2ee
-- title:
--   product first zeroth parts: nm P op U
-- statement:
--   The product first zeroth parts construction uses the nm P op U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L68-L73

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP_opU (ψ : (Fin r → k) → R) (f : Fin r → k) :
    nmP (opU ψ) f = ∑ x ∈ univ.filter (fun x => pair f x = 1), nmV ψ x := by sorry
