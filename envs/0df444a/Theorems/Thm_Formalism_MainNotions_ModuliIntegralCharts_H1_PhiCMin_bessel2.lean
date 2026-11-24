-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_bessel2
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.bessel2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:50.98105+00:00
-- url     : https://prove2.me/theorems/c512b7a1-8686-49f9-be36-a30034b1d514
-- title:
--   Phi CMin: bessel2
-- statement:
--   The Phi CMin construction uses the bessel2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinE.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinE.lean#L11-L21

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open Matrix

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.bessel2 {d : ℕ} (v p q : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) (hp : p ⬝ᵥ p = 1)
    (hpq : p ⬝ᵥ q = 0) (hq : 0 < q ⬝ᵥ q) :
    (v ⬝ᵥ p) ^ 2 * (q ⬝ᵥ q) + (v ⬝ᵥ q) ^ 2 ≤ q ⬝ᵥ q := by sorry
