-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_minor_mem
-- name    : Formalism.DworkPowerSeriesWeights.shape_minor_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:35.021463+00:00
-- url     : https://prove2.me/theorems/c6bef042-a87c-46ba-8691-4bda4e18f554
-- title:
--   Dwork Power Series Weights: shape minor mem
-- statement:
--   The Dwork Power Series Weights construction uses the shape minor mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean#L121-L128

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementH
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.shape_minor_mem {R : Type u} [CommRing R] {J : Type} [Fintype J] [DecidableEq J]
    {N1 p : ℕ} (A : Fin p → J → R) (I : Fin p → Fin N1) (mono : J × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (J × Fin N1) R)).det.support) :
    mono ∈ shapeSet A I := by sorry
