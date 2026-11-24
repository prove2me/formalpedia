-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_strict_pow_eq_zero
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.strict_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:35:48.412884+00:00
-- url     : https://prove2.me/theorems/3e15de06-b392-4548-bf41-4e94e2bc36ca
-- title:
--   Hermitian Projections: strict pow eq zero
-- statement:
--   The Hermitian Projections construction uses the strict pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L109-L113

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections

theorem Formalism.FourierDecayAlt.P.HermitianProjections.strict_pow_eq_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    M ^ m = 0 := by sorry
