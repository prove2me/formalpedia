-- Prove2me | Theorems.Thm_Formalism_UG_P_wact_rowAct_mul
-- name    : Formalism.UG.P.wact_rowAct_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:38:12.0958+00:00
-- url     : https://prove2.me/theorems/d22365de-477c-4e08-9e2e-86dae7d0e3d2
-- title:
--   P: wact row Act mul
-- statement:
--   The P construction uses the wact row Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/DualWeylModuleStable.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/DualWeylModuleStable.lean#L10-L18

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P

theorem Formalism.UG.P.wact_rowAct_mul (R : Type) [CommRing R] (r n : ℕ) (A B : Matrix (Fin r) (Fin r) R) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (A * B) = (Formalism.GradedWeylDivisibility.rowAct R (n := n) B).comp (Formalism.GradedWeylDivisibility.rowAct R A) := by sorry
