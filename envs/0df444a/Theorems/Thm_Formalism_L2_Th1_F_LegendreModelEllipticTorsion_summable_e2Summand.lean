-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_summable_e2Summand
-- name    : Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:49.031177+00:00
-- url     : https://prove2.me/theorems/5d9419e9-6e90-4978-b76c-d7f24e51e1f8
-- title:
--   Legendre Model Elliptic Torsion: summable e2 Summand
-- statement:
--   The Legendre Model Elliptic Torsion construction uses the summable e2 Summand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Legendre.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Legendre.lean#L77-L88

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Legendre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F Formalism.L2.Th1.F.LegendreModelEllipticTorsion

theorem Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand (z : ℍ) : Summable fun n : ℤ => e2Summand n z := by sorry
