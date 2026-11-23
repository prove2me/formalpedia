-- Prove2me | Theorems.Thm_Formalism_FG_FunctionalEquationHom_funEqV_sub
-- name    : Formalism.FG.FunctionalEquationHom.funEqV_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:23.256868+00:00
-- url     : https://prove2.me/theorems/46774dd6-f91d-4bad-9147-70550396b214
-- title:
--   Functional Equation Hom: fun Eq V sub
-- statement:
--   The Functional Equation Hom construction uses the fun Eq V sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationHomVector.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationHomVector.lean#L26-L32

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.FunctionalEquationHom
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.FG.FunctionalEquationHom.funEqV_sub {ι : Type v} [Fintype ι] {τ : Type w} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) {a b : ι → MvPowerSeries τ K} (ha : IsFunEqTypeV p q hq σ M a)
    (hb : IsFunEqTypeV p q hq σ M b) : IsFunEqTypeV p q hq σ M (a - b) := by sorry
