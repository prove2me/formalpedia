-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mem_colSpan_of
-- name    : Formalism.FourierDecayAlt.P.A5x9.mem_colSpan_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:50.562962+00:00
-- url     : https://prove2.me/theorems/e8fa8125-41da-4526-b3af-23943c4eefbe
-- title:
--   A5x9: mem col Span of
-- statement:
--   The A5x9 construction uses the mem col Span of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L529-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L529-L538

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.mem_colSpan_of (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (x : Fin n → R) (hx : x ∈ latZ R (Z₀ * p)) (h0 : abelian₂ R k Z₀ x = 0) : x ∈ colSpan R k Z₀ := by sorry
