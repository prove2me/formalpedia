-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_discr_K
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_K
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:06.469969+00:00
-- url     : https://prove2.me/theorems/df2c0541-34ed-407a-be85-b9435516e35f
-- title:
--   B5: discr K
-- statement:
--   The B5 construction uses the discr K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/LatITopBasis.lean#L216-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/LatITopBasis.lean#L216-L218

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_LatITopBasis
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
open NumberField Polynomial Matrix Classical
open scoped Pointwise

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_K (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) :
    NumberField.discr K = -(d : ℤ) := by sorry
