-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_latI_basis
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latI_basis
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:37:17.452462+00:00
-- url     : https://prove2.me/theorems/f9e317eb-bfb5-44f6-8f2b-9be57b413cd5
-- title:
--   B5: lat I basis
-- statement:
--   The B5 construction uses the lat I basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/IdealBasis.lean#L80-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/IdealBasis.lean#L80-L128

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_IdealBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latI_basis (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (a₀ b₀ : ℂ) (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by sorry
