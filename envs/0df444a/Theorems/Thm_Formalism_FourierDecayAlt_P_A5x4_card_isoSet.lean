-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_card_isoSet
-- name    : Formalism.FourierDecayAlt.P.A5x4.card_isoSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:00.750148+00:00
-- url     : https://prove2.me/theorems/1a6b1888-35f4-421d-b61c-b7dfef9fb66f
-- title:
--   A5x4: card iso Set
-- statement:
--   The A5x4 construction uses the card iso Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L217-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L217-L234

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

theorem Formalism.FourierDecayAlt.P.A5x4.card_isoSet {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z C e lam) = Nat.card (autSet R C e lam) := by sorry
