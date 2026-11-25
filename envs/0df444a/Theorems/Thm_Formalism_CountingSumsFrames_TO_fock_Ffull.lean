-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_Ffull
-- name    : Formalism.CountingSumsFrames.TO.fock_Ffull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:30.879803+00:00
-- url     : https://prove2.me/theorems/2b64fe5b-c67a-4ecb-b273-3147caa74253
-- title:
--   TO: fock Ffull
-- statement:
--   The TO construction uses the fock Ffull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1614-L1619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1614-L1619

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm

theorem Formalism.CountingSumsFrames.TO.fock_Ffull (ρ : Fin r) (n : Fin T.t → ℕ) (f f' : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    fock p (T.Ffull p (LL.setTies T n) i ρ (n i) f) (T.Ffull p (LL.setTies T n) i ρ (n i) f') =
      fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f') := by sorry
