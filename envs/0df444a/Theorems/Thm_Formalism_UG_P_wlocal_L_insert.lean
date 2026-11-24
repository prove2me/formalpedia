-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_L_insert
-- name    : Formalism.UG.P.wlocal_L_insert
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:38.682659+00:00
-- url     : https://prove2.me/theorems/8cd4f7f4-95e8-457a-80fe-a004ead6159b
-- title:
--   P: wlocal L insert
-- statement:
--   The P construction uses the wlocal L insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L166-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L166-L178

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

theorem Formalism.UG.P.wlocal_L_insert {r : ℕ} (k a : Fin r) (c : Fin r → R) (s : Finset (Fin r)) (ha : a ∉ s) (hak : a ≠ k) :
    wlocal_L k (fun i => if i ∈ insert a s then c i else 0) =
      wlocal_E a k (c a) * wlocal_L k (fun i => if i ∈ s then c i else 0) := by sorry
