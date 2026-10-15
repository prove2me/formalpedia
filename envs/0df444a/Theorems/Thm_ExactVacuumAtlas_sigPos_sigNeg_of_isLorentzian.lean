-- Prove2me | Theorems.Thm_ExactVacuumAtlas_sigPos_sigNeg_of_isLorentzian
-- name    : ExactVacuumAtlas.sigPos_sigNeg_of_isLorentzian
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:51:46.77254+00:00
-- url     : https://prove2.me/theorems/df06ca6a-fd60-4430-ab65-67d60f890036
-- title:
--   Lorentzian frames give Mathlib signature $(n,1)$ in dimension $n+1$
-- statement:
--   Let $n$ be a natural number and $G$ a real $(n+1)\times(n+1)$ matrix which is Lorentzian in the sense of bundle `Atlas_Core_Basic`: there is a matrix $E$ with invertible determinant and $E^{\mathsf T}GE=\mathrm{diag}(-1,1,\dots,1)$. Let $Q_G(v)=v^{\mathsf T}Gv$ be the quadratic form of $G$ on $\mathbb R^{n+1}$. Then Mathlib's positive and negative indices of inertia of $Q_G$ are $$\mathrm{sigPos}(Q_G)=n,\qquad \mathrm{sigNeg}(Q_G)=1.$$ (For $n=0$ the form is negative definite on $\mathbb R^1$.)
--
--   Bridge from the local frame-based notion of Lorentzian signature to Mathlib's own signature of a quadratic form (`QuadraticForm` signature in the pinned Mathlib), so that the certificates' signature clause is expressed in a library-native invariant. Only this direction is proved; the converse is not needed and, without symmetry of $G$, is false.
--
--   **Formalization Note** $Q_G$ is `Matrix.toQuadraticForm'`; `sigPos`/`sigNeg` are Mathlib's counts of positive and negative coefficients in an equivalent weighted sum of squares.
-- source:
--   Sylvester's law of inertia (standard linear algebra); Mathlib LinearAlgebra/QuadraticForm/Signature.lean (pinned 0df444a3) for sigPos/sigNeg; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Core/Signature.lean#L52-L68 (module Atlas.Core.Signature, file sha256 24deab1b17221c81185dcc9074681eaeb5d9014f73bf1bf6db43099e2f93278d; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_sigPos_sigNeg_of_isLorentzian.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
open Matrix

theorem ExactVacuumAtlas.sigPos_sigNeg_of_isLorentzian {n : ℕ} {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : IsLorentzian G) : sigPos G.toQuadraticForm' = n ∧ sigNeg G.toQuadraticForm' = 1 := by sorry
