-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_vanish_match
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.vanish_match
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:32.553182+00:00
-- url     : https://prove2.me/theorems/d5ba1b7c-0f9a-4b17-a82e-615e5efdf65c
-- title:
--   Lie Algebra Weight Vectors: vanish match
-- statement:
--   The Lie Algebra Weight Vectors construction uses the vanish match property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/Vanish.lean#L31-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/Vanish.lean#L31-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_Vanish
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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.vanish_match (hBr : Branching) {P : M.Par} (hP : P.OK) {Wp : Type} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    (hz : inWb P.k P.r z) (hT : 0 < Tz P.k P.r z) (hπ : IsType P.k P.r z π P.u)
    {e : Fin (2 * P.r + P.k + 1) → ℂ} (he : inWb P.k P.r e) (hez : herm (Hpk P.k P.r) e z = 0)
    (hee : herm (Hpk P.k P.r) e e = 1) (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hBs : IsFrameOf P.k P.r [z, e] Bs) (hlin : ∀ w : ℂ, IsLinearMap ℂ (capRep P.k P.r π Bs w))
    {x : Wp} (hx : x ≠ 0) (μ : ℂ → ℂ) (hμ : ∀ w : ℂ, capRep P.k P.r π Bs w x = μ (w - ((P.k : ℂ) - 2) / 2) • x) :
    ∃ ρ : M.Ty (Pq P), ∀ Y : ℂ, μ Y = M.xC (Pq P) ρ Y := by sorry
