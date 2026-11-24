-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ib_exists_basis
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ib_exists_basis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:36:57.103811+00:00
-- url     : https://prove2.me/theorems/0ef0bb6e-a995-4574-b5a5-6ba8f10162c5
-- title:
--   B5: ib exists basis
-- statement:
--   The B5 construction uses the ib exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/IdealBasis.lean#L26-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/IdealBasis.lean#L26-L63

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ib_exists_basis {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) :
    ∃ B : Module.Basis (Fin 2) ℤ (𝓞 K), (φ.comp (algebraMap (𝓞 K) K)) (B 0) = a₀ ∧
      (φ.comp (algebraMap (𝓞 K) K)) (B 1) = b₀ := by sorry
