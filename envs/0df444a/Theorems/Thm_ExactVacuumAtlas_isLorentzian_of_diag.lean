-- Prove2me | Theorems.Thm_ExactVacuumAtlas_isLorentzian_of_diag
-- name    : ExactVacuumAtlas.isLorentzian_of_diag
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:20:52.234997+00:00
-- url     : https://prove2.me/theorems/95b98524-c8c9-4d87-8880-1bce2a3872a9
-- title:
--   Diagonal-frame criterion for Lorentzian signature
-- statement:
--   Let $n$ be a natural number, $G$ a real $(n+1)\times(n+1)$ matrix, $E$ a real $(n+1)\times(n+1)$ matrix and $d\in\mathbb R^{n+1}$ with $$E^{\mathsf T}GE=\mathrm{diag}(d_0,\dots,d_n),\qquad d_0<0,\qquad d_i>0\ \ (i\neq0).$$ Then $G$ is *Lorentzian* in the sense of bundle `Atlas_Core_Basic`: there is a matrix $E'$ with invertible determinant and $E'^{\mathsf T}GE'=\eta_n=\mathrm{diag}(-1,1,\dots,1)$. (No invertibility of $E$ is assumed; it follows since the diagonal matrix is invertible.)
--
--   The criterion used by every row to discharge the signature obligation: each row exhibits an explicit (unnormalised) frame that diagonalises its metric with one negative and three positive entries; the normalisation by $1/\sqrt{|d_i|}$ happens once, here.
--
--   **Formalization Note** `IsLorentzian G` is $\exists E,\ \mathrm{IsUnit}(\det E)\wedge E^{\mathsf T}GE=\eta_n$; the total dimension is $n+1$.
-- source:
--   Sylvester's law of inertia (standard linear algebra); Mathlib LinearAlgebra/QuadraticForm/Signature.lean (pinned 0df444a3) for sigPos/sigNeg; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Core/Lorentz.lean#L30-L61 (module Atlas.Core.Lorentz, file sha256 a124a92c2d1eb60bd4324599481f95834c1ae4d958b47b740ed44aa5eff655a4; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_isLorentzian_of_diag.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic

theorem ExactVacuumAtlas.isLorentzian_of_diag {n : ℕ} {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (d : Fin (n + 1) → ℝ)
    (h : E.transpose * G * E = Matrix.diagonal d) (h0 : d 0 < 0)
    (hpos : ∀ i, i ≠ 0 → 0 < d i) : IsLorentzian G := by sorry
