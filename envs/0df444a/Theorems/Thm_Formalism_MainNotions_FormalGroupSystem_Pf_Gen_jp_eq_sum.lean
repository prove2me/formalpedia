-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_jp_eq_sum
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.jp_eq_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:53.225751+00:00
-- url     : https://prove2.me/theorems/c1a9af79-0c88-469d-b153-8079e21c260f
-- title:
--   Gen: jp eq sum
-- statement:
--   The Gen construction uses the jp eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L14-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.jp_eq_sum {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A)
    (f : MvPowerSeries σ K) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jp P f = ∑ κ ∈ S, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • MvPolynomial.coeff κ P := by sorry
