-- Prove2me | Theorems.Thm_Formalism_UG_P_mem_hecke_iff
-- name    : Formalism.UG.P.mem_hecke_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:20:36.071456+00:00
-- url     : https://prove2.me/theorems/cc838fee-3753-43f1-be49-ed67510004d0
-- title:
--   P: mem hecke iff
-- statement:
--   The P construction uses the mem hecke iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckebasic.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckebasic.lean#L56-L57

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]

theorem Formalism.UG.P.mem_hecke_iff (k : Type) [CommRing k] (K : Subgroup G) (f : G → k) :
    f ∈ Hecke k K ↔ IsBiInv K f ∧ FinDosetSupp K f := by sorry
