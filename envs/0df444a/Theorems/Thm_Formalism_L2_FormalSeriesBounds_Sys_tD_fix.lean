-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_tD_fix
-- name    : Formalism.L2.FormalSeriesBounds.Sys.tD_fix
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:29.587283+00:00
-- url     : https://prove2.me/theorems/b5e370af-12e9-5631-9c66-ac2961f58f8e
-- title:
--   Sys: t D fix
-- statement:
--   The Sys construction uses the t D fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L577-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L577-L592

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

theorem Formalism.L2.FormalSeriesBounds.Sys.tD_fix {N1 : ℕ} (D : Formalism.BaseCaseIdentities.Data C (Fin N1) I) (hl : D.l = V.l)
    (hal : ∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x)
    {t : I → MvPowerSeries I C} (ht : S.IsT t) :
    NoConst (fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c)) ∧
      D.Psi (fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c)) =
        fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c) := by sorry
