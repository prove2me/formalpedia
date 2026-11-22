-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_main
-- name    : Formalism.FG.InvIntVAux.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:10.164474+00:00
-- url     : https://prove2.me/theorems/d2e0bb6a-f4e7-4c14-b729-67a7b6c02dfc
-- title:
--   Inv Int VAux: main
-- statement:
--   The Inv Int VAux construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L307-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L307-L411

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
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
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]

theorem Formalism.FG.InvIntVAux.main (ι : Type v) [Fintype ι] [DecidableEq ι]
    (τ : Type w) [Finite τ] (C : (ι → MvPowerSeries τ K) → Prop) (f : ι → MvPowerSeries ι K)
    (hf : IsIdMod2 f)
    (hsub : ∀ a b, C a → C b → C (a - b))
    (hP : ∀ P : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (P i) = 0) →
      (∀ i, IntegralMv (P i)) → C (fun j => MvPowerSeries.subst P (f j)))
    (hlowC : ∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1)
    (h : ι → MvPowerSeries τ K) (hh0 : ∀ i, MvPowerSeries.constantCoeff (h i) = 0)
    (hCh : C (fun j => MvPowerSeries.subst h (f j))) : ∀ i, IntegralMv (h i) := by sorry
