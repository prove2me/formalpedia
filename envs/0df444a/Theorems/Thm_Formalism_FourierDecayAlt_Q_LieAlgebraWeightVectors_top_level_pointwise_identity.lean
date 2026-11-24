-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_top_level_pointwise_identity
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.top_level_pointwise_identity
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:05:25.8403+00:00
-- url     : https://prove2.me/theorems/fadc62e9-6742-42f2-8cfc-34f24ef8b71e
-- title:
--   Lie Algebra Weight Vectors: top level pointwise identity
-- statement:
--   The Lie Algebra Weight Vectors construction uses the top level pointwise identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/TopLevelPointwiseIdentity.lean#L208-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/TopLevelPointwiseIdentity.lean#L208-L218

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.top_level_pointwise_identity (hCap : CapelliIdentityEntry) (hRTA : RightTypeAction) [FiniteDimensional ℂ Wq]
    (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D)
    (hπ'r : IsCRepOn (UWset k r z') π') (hπ'c : ContinuousOn π' (UWset k r z'))
    {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hGG : GGl k r z z' g ≠ 0)
    (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (hBs : IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs) (Y : ℂ) (v : Wq) :
    tL k r z z' (Fin.last r) Y 1 1 F g v = (GGl k r z z' g : ℂ) • F g (capRep k r π' Bs (Y + ((k : ℂ) - 2) / 2) v) := by sorry
