-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_zAct_int
-- name    : Formalism.L2.Pj.QAt.maxCuspsA_zAct_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:38:02.099558+00:00
-- url     : https://prove2.me/theorems/d32702c6-5091-5002-91d3-54867b1095bf
-- title:
--   QAt: max Cusps A z Act int
-- statement:
--   The QAt construction uses the max Cusps A z Act int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L93-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L93-L112

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem Formalism.L2.Pj.QAt.maxCuspsA_zAct_int (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (n : Fin (nZ X ρ) → ℤ) : ∃ β ∈ zGam X cu, ∃ γ ∈ X.Γ,
      (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β ∧
      ∀ y, zAct X cu (fun i => (n i : ℝ)) y = lact γ y := by sorry
