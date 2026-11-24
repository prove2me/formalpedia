-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_cplx_str_core
-- name    : Formalism.L2.Pj.DatLin.cplx_str_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:17.824111+00:00
-- url     : https://prove2.me/theorems/f81cf651-3135-4095-b7ed-bfa222f69dd3
-- title:
--   Dat Lin: cplx str core
-- statement:
--   The Dat Lin construction uses the cplx str core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L24-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L24-L51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {m : Type} [Fintype m] [DecidableEq m]

theorem Formalism.L2.Pj.DatLin.cplx_str_core (H P Q J : Matrix m m ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hJ2 : J * J = 1) (hJh : Jᴴ = J) (hH : Pᴴ * H * P = J) :
    let K := P * (Complex.I • J) * Q
    (K * K = -1) ∧ (Kᴴ * H * K = H) ∧ (Kᴴ * H = (-Complex.I) • (Qᴴ * Q)) ∧
      K.trace = Complex.I * J.trace := by sorry
