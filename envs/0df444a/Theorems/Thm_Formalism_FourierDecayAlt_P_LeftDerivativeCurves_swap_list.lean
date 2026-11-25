-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_swap_list
-- name    : Formalism.FourierDecayAlt.P.LeftDerivativeCurves.swap_list
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:17.547148+00:00
-- url     : https://prove2.me/theorems/27ceec85-5f34-57d3-baf7-54f1fd9b7026
-- title:
--   Left Derivative Curves: swap list
-- statement:
--   The Left Derivative Curves construction uses the swap list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L189-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L189-L210

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.LeftDerivativeCurves.swap_list {g₀ : Mx k r} (hg₀ : g₀ ∈ Glev k r i ∩ D)
    (L : List (((Mx k r → E) → Mx k r → E) × ((Mx k r → E) → Mx k r → E)))
    (hA : ∀ p ∈ L, Good k r i D p.1) (hB : ∀ p ∈ L, Good k r i D p.2)
    (hpt : ∀ p ∈ L, ∀ f, p.1 f g₀ = p.2 f g₀) (hc : ∀ p ∈ L, ∀ q ∈ L, Comm k r i D q.2 p.1) :
    ∀ f, SmoothLev k r i D f →
      (L.map Prod.fst).foldr (fun T h => T h) f g₀ = (L.map Prod.snd).foldl (fun h T => T h) f g₀ := by sorry
