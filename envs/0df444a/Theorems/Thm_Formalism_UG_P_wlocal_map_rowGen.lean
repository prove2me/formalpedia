-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_map_rowGen
-- name    : Formalism.UG.P.wlocal_map_rowGen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:38:30.606708+00:00
-- url     : https://prove2.me/theorems/a90003c9-2664-42e0-bd4a-a7a114f1bab0
-- title:
--   P: wlocal map row Gen
-- statement:
--   The P construction uses the wlocal map row Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L383-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L383-L392

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

theorem Formalism.UG.P.wlocal_map_rowGen (φ : R →+* S) {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen S a b (map φ f) = Polynomial.map (map φ) (rowGen R a b f) := by sorry
