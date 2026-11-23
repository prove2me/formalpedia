-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_map_applyWord
-- name    : Formalism.UG.P.wlocal_map_applyWord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:37.961015+00:00
-- url     : https://prove2.me/theorems/72e796cd-9da0-4dfc-be06-774e17bd841d
-- title:
--   P: wlocal map apply Word
-- statement:
--   The P construction uses the wlocal map apply Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L399-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L399-L407

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
variable {R S : Type} [CommRing R] [CommRing S]

theorem Formalism.UG.P.wlocal_map_applyWord (φ : R →+* S) {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (applyWord R w f) = applyWord S w (map φ f) := by sorry
