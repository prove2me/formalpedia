-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_moment
-- name    : Formalism.NuclearRankWeightBounds.P.moment
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:10.0888+00:00
-- url     : https://prove2.me/theorems/12de0efb-a2e5-47a5-adb8-40906aafa6b9
-- title:
--   P: moment
-- statement:
--   The P construction uses the moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DetMulDiagonalMulEqSum.lean#L50-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DetMulDiagonalMulEqSum.lean#L50-L74

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset

theorem Formalism.NuclearRankWeightBounds.P.moment {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (A : Matrix (Fin k) n ℂ)
    (hA : A * Aᴴ = 1) (ν : n → ℂ) (m : ℕ) :
    ∑ J ∈ powersetCard k (univ : Finset n),
      (∏ j ∈ J, (1 + X * C (ν j))).coeff m *
        ((Aᴴ * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))).det
    = (det (1 + (X : ℂ[X]) • (A * diagonal ν * Aᴴ).map C)).coeff m := by sorry
