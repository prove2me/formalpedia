-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Ker_mk_eq_iff
-- name    : Formalism.L2.Th1.F.Ker.mk_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:09.937021+00:00
-- url     : https://prove2.me/theorems/f89fbd32-a5e5-46e0-8f1c-cb7f3d5ad0b6
-- title:
--   Ker: mk eq iff
-- statement:
--   The Ker construction uses the mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MulStableIntegral.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MulStableIntegral.lean#L115-L125

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
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
open Formalism.L2.Th1.F.Ker

theorem Formalism.L2.Th1.F.Ker.mk_eq_iff (L : PeriodPair) (α : ℂ) (h : MulStable L α) (u v : L.lattice) :
    (Submodule.Quotient.mk u : L.lattice ⧸ LinearMap.range (mulEnd L α h)) = Submodule.Quotient.mk v ↔
      ∃ x ∈ L.lattice, (u : ℂ) - v = α * x := by sorry
