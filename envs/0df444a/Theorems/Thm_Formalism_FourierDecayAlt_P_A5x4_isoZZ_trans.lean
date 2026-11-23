-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_trans
-- name    : Formalism.FourierDecayAlt.P.A5x4.isoZZ_trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:18.264595+00:00
-- url     : https://prove2.me/theorems/0e9770eb-7178-4054-86ad-57616d93e0ca
-- title:
--   A5x4: iso ZZ trans
-- statement:
--   The A5x4 construction uses the iso ZZ trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L367-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L367-L375

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x4.isoZZ_trans {n n' n'' : ℕ} {Z : Matrix (Fin n) (Fin n) K}
    {Z' : Matrix (Fin n') (Fin n') K} {Z'' : Matrix (Fin n'') (Fin n'') K}
    {φ : coker R Z ≃ₗ[R] coker R Z'} {φ' : coker R Z' ≃ₗ[R] coker R Z''}
    (h : φ ∈ isoZZ R Z Z') (h' : φ' ∈ isoZZ R Z' Z'') : φ.trans φ' ∈ isoZZ R Z Z'' := by sorry
