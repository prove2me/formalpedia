-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_aeval_eig
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.aeval_eig
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:18.37328+00:00
-- url     : https://prove2.me/theorems/e74d56a8-31a7-404a-8d0b-3f5b1fb44d16
-- title:
--   Fr Tan Alg: aeval eig
-- statement:
--   The Fr Tan Alg construction uses the aeval eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L24-L28

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
variable {S M : Type} [Field S] [AddCommGroup M] [Module S M]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.aeval_eig (f : Module.End S M) (μ : S) (x : M) (hx : f x = μ • x) (p : S[X]) :
    aeval f p x = p.eval μ • x := by sorry
