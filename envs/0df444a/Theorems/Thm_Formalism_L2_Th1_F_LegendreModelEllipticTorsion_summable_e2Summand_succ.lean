-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_summable_e2Summand_succ
-- name    : Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:25.760976+00:00
-- url     : https://prove2.me/theorems/010b6663-7dee-43b0-b14c-c3555a62dfa1
-- title:
--   Legendre Model Elliptic Torsion: summable e2 Summand succ
-- statement:
--   The Legendre Model Elliptic Torsion construction uses the summable e2 Summand succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Legendre.lean#L39-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Legendre.lean#L39-L75

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

theorem Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand_succ (z : ℍ) : Summable fun a : ℕ => e2Summand ((a : ℤ) + 1) z := by sorry
