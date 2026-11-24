-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_eisenstein_G6_closure
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.eisenstein_G6_closure
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:34.496857+00:00
-- url     : https://prove2.me/theorems/674dc96e-00c7-4775-8585-32f8ca2f5e49
-- title:
--   B5: eisenstein G6 closure
-- statement:
--   The B5 construction uses the eisenstein G6 closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Jacobi.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Jacobi.lean#L105-L112

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.eisenstein_G6_closure (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    eisG (AddSubgroup.closure {a, a * z}) 3 =
      (a ^ 6)⁻¹ * (2 * ((Real.pi : ℂ) ^ 6 / 945) * ModularForm.E₆ (⟨z, hz⟩ : UpperHalfPlane)) := by sorry
