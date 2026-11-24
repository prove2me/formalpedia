-- Prove2me | Theorems.Thm_Formalism_UG_P_map_mulVec_mem_stdLat
-- name    : Formalism.UG.P.map_mulVec_mem_stdLat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:32:56.656942+00:00
-- url     : https://prove2.me/theorems/7fcadfaa-a8f4-4f01-8ec1-0136be97a3b5
-- title:
--   P: map mul Vec mem std Lat
-- statement:
--   The P construction uses the map mul Vec mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean#L16-L26

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.map_mulVec_mem_stdLat (M : Matrix n n R) (x : n → A)
    (hx : x ∈ stdLat (n := n) (A := A) R) :
    (M.map (algebraMap R A)) *ᵥ x ∈ stdLat (n := n) (A := A) R := by sorry
