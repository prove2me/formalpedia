-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_rowAct_mul
-- name    : Formalism.UG.P.wlocal_rowAct_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:28.978631+00:00
-- url     : https://prove2.me/theorems/b71530ff-4ad1-496e-9bcc-5046ee835393
-- title:
--   P: wlocal row Act mul
-- statement:
--   The P construction uses the wlocal row Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L30-L38

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]

theorem Formalism.UG.P.wlocal_rowAct_mul {r n : ℕ} (A B : Matrix (Fin r) (Fin r) R) :
    rowAct R (n := n) (A * B) = (rowAct R B).comp (rowAct R A) := by sorry
