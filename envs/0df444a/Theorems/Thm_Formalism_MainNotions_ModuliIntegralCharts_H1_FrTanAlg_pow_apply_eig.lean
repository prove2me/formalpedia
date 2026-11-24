-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_pow_apply_eig
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.pow_apply_eig
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:12.817174+00:00
-- url     : https://prove2.me/theorems/be418045-3d46-49e5-b745-1183599183b0
-- title:
--   Fr Tan Alg: pow apply eig
-- statement:
--   The Fr Tan Alg construction uses the pow apply eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L15-L22

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.pow_apply_eig (f : Module.End S M) (μ : S) (x : M) (hx : f x = μ • x) (k : ℕ) :
    (f ^ k) x = μ ^ k • x := by sorry
