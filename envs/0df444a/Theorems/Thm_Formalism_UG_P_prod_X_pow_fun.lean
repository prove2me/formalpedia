-- Prove2me | Theorems.Thm_Formalism_UG_P_prod_X_pow_fun
-- name    : Formalism.UG.P.prod_X_pow_fun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:02.46617+00:00
-- url     : https://prove2.me/theorems/5cddb0c5-50ec-489a-a81e-5e6425711742
-- title:
--   P: prod X pow fun
-- statement:
--   The P construction uses the prod X pow fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LinSubstIsHomogeneous.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LinSubstIsHomogeneous.lean#L41-L45

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
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
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.prod_X_pow_fun (β : n → ℕ) :
    (∏ j, X j ^ β j : MvPolynomial n O) = monomial (Finsupp.equivFunOnFinite.symm β) 1 := by sorry
