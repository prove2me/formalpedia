-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_hom_basis
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.hom_basis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:43.696829+00:00
-- url     : https://prove2.me/theorems/70f2ea9b-b988-4ce6-b393-09445ea1e44c
-- title:
--   Fr Tan Dir Alg: hom basis
-- statement:
--   The Fr Tan Dir Alg construction uses the hom basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean#L15-L20

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
variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.hom_basis {R' : Type} [Ring R'] (f : 𝓞 E →+* R') (b : Module.Basis κ ℤ (𝓞 E)) (x : 𝓞 E) :
    f x = ∑ k, ((b.repr x k : ℤ) : R') * f (b k) := by sorry
