-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_kill
-- name    : Formalism.UG.P.wlocal_kill
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:38:30.854977+00:00
-- url     : https://prove2.me/theorems/16e68cff-1557-4502-be21-f7a9122f51b4
-- title:
--   P: wlocal kill
-- statement:
--   The P construction uses the wlocal kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L465-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L465-L484

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.UG.P.wlocal_kill (P : Ideal R) [P.IsPrime] {σ : Type} (w : MvPolynomial σ R)
    (hw : map (algebraMap R (Localization.AtPrime P)) w = 0) :
    ∃ t ∈ P.primeCompl, C t * w = 0 := by sorry
