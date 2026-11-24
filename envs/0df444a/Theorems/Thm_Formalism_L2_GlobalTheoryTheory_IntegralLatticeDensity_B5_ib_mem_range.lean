-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ib_mem_range
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ib_mem_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:36:54.948724+00:00
-- url     : https://prove2.me/theorems/58d496ce-229c-4792-aaf6-f923598e6f45
-- title:
--   B5: ib mem range
-- statement:
--   The B5 construction uses the ib mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/IdealBasis.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/IdealBasis.lean#L13-L24

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ib_mem_range {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (w : ℂ)
    (hw : w ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ)) :
    ∃ c : 𝓞 K, (φ.comp (algebraMap (𝓞 K) K)) c = w := by sorry
