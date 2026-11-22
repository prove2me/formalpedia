-- Prove2me | Theorems.Thm_Formalism_UG_P_heckecomm_tr_val
-- name    : Formalism.UG.P.heckecomm_tr_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:31:13.51082+00:00
-- url     : https://prove2.me/theorems/8525ceb9-8b29-4f54-9f9a-6d6d9919b05e
-- title:
--   P: heckecomm tr val
-- statement:
--   The P construction uses the heckecomm tr val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckecomm.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckecomm.lean#L83-L84

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {R : Type} [CommRing R] {n : ℕ}

theorem Formalism.UG.P.heckecomm_tr_val (g : GL (Fin n) R) :
    ((heckecomm_tr g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Matrix.transpose (g : Matrix (Fin n) (Fin n) R) := by sorry
