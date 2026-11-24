-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_Ffull_indep
-- name    : Formalism.CountingSumsFrames.TO.Ffull_indep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:49.896801+00:00
-- url     : https://prove2.me/theorems/1e2c5530-fa41-4bd3-b807-1cc809cc9447
-- title:
--   TO: Ffull indep
-- statement:
--   The TO construction uses the Ffull indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2418-L2452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2418-L2452

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
include hρ
omit hρ

theorem Formalism.CountingSumsFrames.TO.Ffull_indep (Ω : Finset (Fin r → ℤ)) (nb : (Fin r → ℤ) → ℕ)
    (f : ∀ w, Fin (nb w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : ∀ w a, f w a ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hli : ∀ w, LinearIndependent ℚ_[p] (f w)) :
    LinearIndependent ℚ_[p] (fun x : (Σ w : Ω, Fin (nb w.1)) => T.Ffull p (LL.setTies T n) i ρ (n i) (f x.1.1 x.2)) := by sorry
