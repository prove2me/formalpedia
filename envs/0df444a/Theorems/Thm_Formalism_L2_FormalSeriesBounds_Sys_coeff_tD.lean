-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_coeff_tD
-- name    : Formalism.L2.FormalSeriesBounds.Sys.coeff_tD
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:26:51.213867+00:00
-- url     : https://prove2.me/theorems/786cecdd-6ef6-4812-99c5-ad40859180ab
-- title:
--   Sys: coeff t D
-- statement:
--   The Sys construction uses the coeff t D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L477-L572
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L477-L572

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem Formalism.L2.FormalSeriesBounds.Sys.coeff_tD (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t)
    (al' : I → ℕ → I → C) (zc : τ → I → C)
    (hal : ∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al' c k b * S.al b 0 x)
    (hW : ∀ β x, W β x = ∑ b, zc β b * S.al b 0 x) (b : I) (A : τ →₀ ℕ) :
    coeff A (subst (linS W) (t b)) =
      coeff A (∑ β, MvPowerSeries.C (zc β b) * (X β : MvPowerSeries τ C)) -
        ∑ c, ∑ j ∈ Finset.Icc 1 A.degree,
          al' c j b * coeff A (subst (linS W) (t c) ^ (V.l ^ j)) := by sorry
