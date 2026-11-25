-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_max_cusps_rank_one_expand
-- name    : Formalism.L2.Pj.QAt.max_cusps_rank_one_expand
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:32:39.430858+00:00
-- url     : https://prove2.me/theorems/d6812699-e60e-4aa0-b6c0-900de78e5e3b
-- title:
--   QAt: max cusps rank one expand
-- statement:
--   The QAt construction uses the max cusps rank one expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L14-L28

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

theorem Formalism.L2.Pj.QAt.max_cusps_rank_one_expand {R : Type} [CommRing R] (σ : R →+* R) {r ρ : ℕ}
    (G : Matrix (Fin r) (Fin r) R) (η : Fin ρ → R) (e : Fin ρ → Fin r → R) (α : R) (a b : Fin r) :
    α * (∑ a', η a' * e a' a) * ∑ k, G b k * σ (∑ b', η b' * e b' k) =
      ∑ a', ∑ b', α * (η a' * σ (η b')) * e a' a * ∑ k, G b k * σ (e b' k) := by sorry
