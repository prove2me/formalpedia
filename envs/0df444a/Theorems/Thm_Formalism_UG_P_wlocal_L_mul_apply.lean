-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_L_mul_apply
-- name    : Formalism.UG.P.wlocal_L_mul_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:31.273465+00:00
-- url     : https://prove2.me/theorems/6bb4ab44-3bd2-40be-b3c1-6e6d89d61fcb
-- title:
--   P: wlocal L mul apply
-- statement:
--   The P construction uses the wlocal L mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L26-L28

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

theorem Formalism.UG.P.wlocal_L_mul_apply {r : ℕ} (k : Fin r) (c : Fin r → R) (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (wlocal_L k c * M) i j = M i j + (if i ≠ k then c i * M k j else 0) := by sorry
