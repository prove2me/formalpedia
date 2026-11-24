-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_hasDerivAt_psi
-- name    : Formalism.L2.Th1.F.S2IsogenyPsi.hasDerivAt_psi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:40.438345+00:00
-- url     : https://prove2.me/theorems/f664860e-fb1b-4f57-b500-c407ffcad30f
-- title:
--   S2 Isogeny Psi: has Deriv At psi
-- statement:
--   The S2 Isogeny Psi construction uses the has Deriv At psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstIsogeny.lean#L51-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstIsogeny.lean#L51-L78

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.S2IsogenyPsi

theorem Formalism.L2.Th1.F.S2IsogenyPsi.hasDerivAt_psi (hP : IsogenyP) (hd : ZetaHasDeriv) (L : PeriodPair) (α : ℂ) (S : Finset ℂ)
    (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S) (z : ℂ) (hz : α * z ∉ L.lattice) :
    HasDerivAt (psi L α S) 0 z := by sorry
