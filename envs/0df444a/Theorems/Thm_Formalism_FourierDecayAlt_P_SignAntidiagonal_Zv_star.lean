-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_Zv_star
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.Zv_star
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:28:56.672528+00:00
-- url     : https://prove2.me/theorems/36430413-1f96-5daf-b434-45f2ea6c255a
-- title:
--   Sign Antidiagonal: Zv star
-- statement:
--   The Sign Antidiagonal construction uses the Zv star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L109-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L109-L130

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.Zv_star (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hy0 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hdet : (Ym k r j hj y).det ≠ 0) (b : Fin j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    Zv k r j hj y b q = if b.val = 2 * r + k - q.val then 1 else 0 := by sorry
