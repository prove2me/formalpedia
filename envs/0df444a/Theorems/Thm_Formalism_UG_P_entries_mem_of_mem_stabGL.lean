-- Prove2me | Theorems.Thm_Formalism_UG_P_entries_mem_of_mem_stabGL
-- name    : Formalism.UG.P.entries_mem_of_mem_stabGL
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:21.379426+00:00
-- url     : https://prove2.me/theorems/8bc15723-4a89-42fc-b919-d479fd671b6a
-- title:
--   P: entries mem of mem stab GL
-- statement:
--   The P construction uses the entries mem of mem stab GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean#L28-L39

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

theorem Formalism.UG.P.entries_mem_of_mem_stabGL (h : GL n A) (hh : h ∈ stabGL (stdLat (n := n) (A := A) R))
    (i j : n) : (h : Matrix n n A) i j ∈ Set.range (algebraMap R A) := by sorry
