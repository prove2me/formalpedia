-- Prove2me | Theorems.Thm_Formalism_UG_P_stabilizer_coset_eq
-- name    : Formalism.UG.P.stabilizer_coset_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:36:45.800615+00:00
-- url     : https://prove2.me/theorems/d7f964de-6114-4005-a407-62ecbcee64b4
-- title:
--   P: stabilizer coset eq
-- statement:
--   The P construction uses the stabilizer coset eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AssocFin.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AssocFin.lean#L15-L28

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
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
open Formalism.UG
variable {G : Type} [Group G] (K : Subgroup G)

theorem Formalism.UG.P.stabilizer_coset_eq (s : G) :
    MulAction.stabilizer K ((s : G ⧸ K)) = (K.map (MulAut.conj s).toMonoidHom).subgroupOf K := by sorry
