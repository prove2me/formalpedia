-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_relIndex_unipotent_conj_symm
-- name    : Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.relIndex_unipotent_conj_symm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:31.238281+00:00
-- url     : https://prove2.me/theorems/3c321716-c45b-566b-a456-8d5485d06323
-- title:
--   Filt: rel Index unipotent conj symm
-- statement:
--   The Filt construction uses the rel Index unipotent conj symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexUnipotentConjSymm.lean#L48-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexUnipotentConjSymm.lean#L48-L61

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_FiltRelIndex
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexUnipotentConjSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K] (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))

theorem Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.relIndex_unipotent_conj_symm (hLF : L ≤ FG n K 0) (X : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) (hg : g ∈ L) (hX : X ≤ L) :
    X.relIndex (cj g X) = (cj g X).relIndex X := by sorry
