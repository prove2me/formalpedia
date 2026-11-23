-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
-- name    : Formalism.L2.Th1.F.LegendreModelEllipticTorsion.key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:12.849206+00:00
-- url     : https://prove2.me/theorems/48e5a586-66c4-4ea3-bf22-fe6a1fcb5dc4
-- title:
--   Legendre Model Elliptic Torsion: key
-- statement:
--   The Legendre Model Elliptic Torsion construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Legendre.lean#L146-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Legendre.lean#L146-L161

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

theorem Formalism.L2.Th1.F.LegendreModelEllipticTorsion.key (u v : ℂ) (h : 0 < (v / u).im) :
    (u * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) * v
      - (v * ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) * u = 2 * π * I := by sorry
