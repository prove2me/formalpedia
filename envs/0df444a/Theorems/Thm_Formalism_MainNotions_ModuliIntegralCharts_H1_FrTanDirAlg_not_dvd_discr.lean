-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_not_dvd_discr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.not_dvd_discr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:55.351043+00:00
-- url     : https://prove2.me/theorems/b04cb6a4-4e43-4c84-b1f6-8841b2d618ff
-- title:
--   Fr Tan Dir Alg: not dvd discr
-- statement:
--   The Fr Tan Dir Alg construction uses the not dvd discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L130-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L130-L196

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.not_dvd_discr (g : ℕ) (hg : g.Prime)
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup) :
    ¬ (g : ℤ) ∣ discr E := by sorry
