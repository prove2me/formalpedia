-- Prove2me | Theorems.Thm_DyckAlgebra_thetaDescent_mk
-- name    : DyckAlgebra.thetaDescent_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:24:41.944162+00:00
-- url     : https://prove2.me/theorems/83635bd9-6edf-41b2-a2e1-e644249fd74a
-- title:
--   Dyck Algebra: theta Descent mk
-- statement:
--   The Dyck Algebra construction uses the theta Descent mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/ThetaDescent.lean#L40-L46
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/ThetaDescent.lean#L40-L46

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_ThetaDescent
set_option autoImplicit true
open DyckAlgebra
universe v
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜}
variable {C : Type v} [Ring C] [Algebra 𝕜 C]

theorem DyckAlgebra.thetaDescent_mk (thetaGen : Gen → C)
    (preserves : ∀ ⦃a b : Pre 𝕜⦄, Rel q t a b →
      thetaPre thetaGen a = thetaPre thetaGen b)
    (a : Pre 𝕜) :
    thetaDescent thetaGen preserves (RingQuot.mkAlgHom 𝕜 (Rel q t) a) =
      thetaPre thetaGen a := by sorry
