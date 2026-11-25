-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_coeff_subst_ze
-- name    : Formalism.L2.FormalSeriesBounds.Sys.coeff_subst_ze
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:27.215693+00:00
-- url     : https://prove2.me/theorems/48a9d422-b87f-563b-837b-001a0084d2bc
-- title:
--   Sys: coeff subst ze
-- statement:
--   The Sys construction uses the coeff subst ze property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L464-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L464-L475

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)
variable {τ : Type} [Fintype τ]

theorem Formalism.L2.FormalSeriesBounds.Sys.coeff_subst_ze (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t) (κ : J)
    (A : τ →₀ ℕ) :
    coeff A (subst (linS W) (S.ze t κ)) =
      -∑ c, ∑ j ∈ Finset.Icc 1 A.degree,
        S.be c j κ * coeff A (subst (linS W) (t c) ^ (V.l ^ j)) := by sorry
