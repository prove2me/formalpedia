-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_kill_alt_alt
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.kill_alt_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:39.72111+00:00
-- url     : https://prove2.me/theorems/d6a3645d-2ea0-49c0-a6b6-dbcd837b0592
-- title:
--   Exp Uniq Jet: kill alt alt
-- statement:
--   The Exp Uniq Jet construction uses the kill alt alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L200-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L200-L203

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]
variable {n : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.kill_alt_alt (m : ℕ) (i : Fin 2) (v : Fin 2 × Fin n) :
    kill (R := R) m i (zz m v) = if v.1 = i then 0 else zz m v := by sorry
