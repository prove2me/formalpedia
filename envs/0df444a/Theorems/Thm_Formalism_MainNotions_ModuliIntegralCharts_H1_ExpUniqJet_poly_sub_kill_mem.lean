-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_poly_sub_kill_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.poly_sub_kill_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:00:42.213141+00:00
-- url     : https://prove2.me/theorems/b65515f8-2237-4ccf-8839-0e8c5036714f
-- title:
--   Exp Uniq Jet: poly sub kill mem
-- statement:
--   The Exp Uniq Jet construction uses the poly sub kill mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L205-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L205-L227

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.poly_sub_kill_mem (i : Fin 2) (P : MvPolynomial (Fin 2 × Fin n) R) :
    P - aeval (killS i) P ∈ Ideal.span (Set.range fun j : Fin n => (X (i, j) : MvPolynomial (Fin 2 × Fin n) R)) := by sorry
