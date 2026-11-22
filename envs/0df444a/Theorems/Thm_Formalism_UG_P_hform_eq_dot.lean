-- Prove2me | Theorems.Thm_Formalism_UG_P_hform_eq_dot
-- name    : Formalism.UG.P.hform_eq_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:15.120103+00:00
-- url     : https://prove2.me/theorems/7f6cd21b-93ce-4692-9078-8cb8793be483
-- title:
--   P: hform eq dot
-- statement:
--   The P construction uses the hform eq dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Bridge.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Bridge.lean#L15-L20

import Definitions.Def_Formalism_SatakeDualWeyl_StatementB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
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

theorem Formalism.UG.P.hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y : n → A) : Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by sorry
