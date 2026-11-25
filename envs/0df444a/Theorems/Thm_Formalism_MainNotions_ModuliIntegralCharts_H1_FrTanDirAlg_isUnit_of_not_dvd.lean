-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_isUnit_of_not_dvd
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.isUnit_of_not_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:04.606648+00:00
-- url     : https://prove2.me/theorems/1fcb2086-d3f5-4c13-8658-813e58365227
-- title:
--   Fr Tan Dir Alg: is Unit of not dvd
-- statement:
--   The Fr Tan Dir Alg construction uses the is Unit of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L198-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L198-L208

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
open NumberField Matrix
variable (E : Type) [Field E] [NumberField E]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.isUnit_of_not_dvd {V : Type} [CommRing V] [IsLocalRing V] (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (d : ℤ) (hd : ¬ (g : ℤ) ∣ d) : IsUnit (d : V) := by sorry
