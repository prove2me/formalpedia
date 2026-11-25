-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormSums_ec_sum
-- name    : Formalism.FourierDecayAlt.P.HermitianFormSums.ec_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:09:39.544485+00:00
-- url     : https://prove2.me/theorems/f6b86d97-11af-4647-a3fc-9ad9f8d75716
-- title:
--   Hermitian Form Sums: ec sum
-- statement:
--   The Hermitian Form Sums construction uses the ec sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L124-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L124-L137

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.HermitianFormSums
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.HermitianFormSums.ec_sum (hE : Formalism.FourierDecayAlt.Qr.EcLie) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hπ : IsRepW k r z π) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (Z : ι → Mx k r) (hZ : ∀ i, InGlW k r z (Z i)) (Z0 : Mx k r) (h0 : InGlW k r z Z0) :
    InGlW k r z (∑ i ∈ s, c i • Z i) ∧ ecOp π (∑ i ∈ s, c i • Z i) = ∑ i ∈ s, c i • ecOp π (Z i) := by sorry
