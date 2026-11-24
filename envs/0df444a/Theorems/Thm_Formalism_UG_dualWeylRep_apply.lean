-- Prove2me | Theorems.Thm_Formalism_UG_dualWeylRep_apply
-- name    : Formalism.UG.dualWeylRep_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:18.592834+00:00
-- url     : https://prove2.me/theorems/60370a1b-14cd-43ec-9f97-fb6dd1395dc8
-- title:
--   UG: dual Weyl Rep apply
-- statement:
--   The UG construction uses the dual Weyl Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/DualWeylRepApply.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/DualWeylRepApply.lean#L50-L53

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_SatakeDualWeyl_DualWeylRepApply
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
open Formalism Formalism.UG

theorem Formalism.UG.dualWeylRep_apply (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (g : GL (Fin r) R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    ((dualWeylRep R r n ν g f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : MvPolynomial (Fin r × Fin n) R) =
      dwAct R r n g f := by sorry
