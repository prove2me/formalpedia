-- Prove2me | Theorems.Thm_ExactVacuumAtlas_sigPos_sigNeg_four
-- name    : ExactVacuumAtlas.sigPos_sigNeg_four
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:51:54.951918+00:00
-- url     : https://prove2.me/theorems/cbe3e4ca-786d-4c4a-accf-1b88dc54de67
-- title:
--   Four-dimensional Lorentzian frames give Mathlib signature $(3,1)$
-- statement:
--   Let $G$ be a real $4\times4$ matrix which is Lorentzian in the sense of bundle `Atlas_Core_Basic` (there is $E$ with invertible determinant and $E^{\mathsf T}GE=\mathrm{diag}(-1,1,1,1)$) and $Q_G(v)=v^{\mathsf T}Gv$. Then $$\mathrm{sigPos}(Q_G)=3,\qquad \mathrm{sigNeg}(Q_G)=1.$$
--
--   The four-dimensional instance of the signature bridge, fixing the convention $(3,1)$ used throughout the atlas; a release target alongside the goal theorem.
-- source:
--   Sylvester's law of inertia (standard linear algebra); Mathlib LinearAlgebra/QuadraticForm/Signature.lean (pinned 0df444a3) for sigPos/sigNeg; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Core/Signature.lean#L70-L73 (module Atlas.Core.Signature, file sha256 24deab1b17221c81185dcc9074681eaeb5d9014f73bf1bf6db43099e2f93278d; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_sigPos_sigNeg_four.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
open Matrix

theorem ExactVacuumAtlas.sigPos_sigNeg_four {G : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzian G) :
    sigPos G.toQuadraticForm' = 3 ∧ sigNeg G.toQuadraticForm' = 1 := by sorry
