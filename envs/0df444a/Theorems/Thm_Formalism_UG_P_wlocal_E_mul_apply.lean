-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_E_mul_apply
-- name    : Formalism.UG.P.wlocal_E_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:29:13.831299+00:00
-- url     : https://prove2.me/theorems/12d74035-c46a-44ee-8d33-fd28f475d79f
-- title:
--   P: wlocal E mul apply
-- statement:
--   The P construction uses the wlocal E mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L22-L24

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

theorem Formalism.UG.P.wlocal_E_mul_apply {r : ℕ} (a b : Fin r) (c : R) (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (wlocal_E a b c * M) i j = M i j + (if i = a then c * M b j else 0) := by sorry
