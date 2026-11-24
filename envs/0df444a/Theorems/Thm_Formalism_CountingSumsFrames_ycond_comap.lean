-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ycond_comap
-- name    : Formalism.CountingSumsFrames.ycond_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:37.189155+00:00
-- url     : https://prove2.me/theorems/2c0b701f-d820-4cf7-b0d5-26720b64b56c
-- title:
--   Counting Sums Frames: ycond comap
-- statement:
--   The Counting Sums Frames construction uses the ycond comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1583-L1606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1583-L1606

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.ycond_comap [NeZero r] {M' : ℕ} (LA : Letters M') (LB : Letters N) (ι : Fin M' → Fin N)
    (hι : ∀ a, ((ι a) : ℕ) = a) (hv : ∀ a, LB.vec (ι a) = LA.vec a)
    (hinj : Function.Injective (fun x : Fin M' × Fin r => (ι x.1, x.2))) (j : ℕ) (Mth : WithTop ℤ)
    (hwv : (wv LB j) ∘ (fun x : Fin M' × Fin r => (ι x.1, x.2)) = wv LA j)
    {F' : MvPolynomial (Fin M' × Fin r) ℚ_[p]}
    (hF : rename (fun x : Fin M' × Fin r => (ι x.1, x.2)) F' ∈ YCond p LB j Mth) : F' ∈ YCond p LA j Mth := by sorry
