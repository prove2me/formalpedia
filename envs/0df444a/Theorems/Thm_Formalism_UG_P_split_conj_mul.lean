-- Prove2me | Theorems.Thm_Formalism_UG_P_split_conj_mul
-- name    : Formalism.UG.P.split_conj_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:10.96483+00:00
-- url     : https://prove2.me/theorems/9a49955a-480f-4aef-baa2-13c37effd9c1
-- title:
--   P: split conj mul
-- statement:
--   The P construction uses the split conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L64-L70

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.split_conj_mul (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) {P Q : Matrix n n R}
    (hPQ : P * Q = 1) : (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = 1 := by sorry
