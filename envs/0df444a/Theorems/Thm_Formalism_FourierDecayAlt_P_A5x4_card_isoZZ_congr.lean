-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_card_isoZZ_congr
-- name    : Formalism.FourierDecayAlt.P.A5x4.card_isoZZ_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:48:39.095375+00:00
-- url     : https://prove2.me/theorems/3fbf253d-8f04-4336-bc1a-82c6dcea5d3a
-- title:
--   A5x4: card iso ZZ congr
-- statement:
--   The A5x4 construction uses the card iso ZZ congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L377-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L377-L388

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

theorem Formalism.FourierDecayAlt.P.A5x4.card_isoZZ_congr {n n' m m' : ℕ} {A : Matrix (Fin n) (Fin n) K}
    {A' : Matrix (Fin n') (Fin n') K} {B : Matrix (Fin m) (Fin m) K}
    {B' : Matrix (Fin m') (Fin m') K}
    {φ1 : coker R A ≃ₗ[R] coker R A'} {φ2 : coker R B ≃ₗ[R] coker R B'}
    (h1 : φ1 ∈ isoZZ R A A') (h2 : φ2 ∈ isoZZ R B B') :
    Nat.card (isoZZ R A B) = Nat.card (isoZZ R A' B') := by sorry
