-- Prove2me | Theorems.Thm_BianchiIX_basis_det_cons_normal_independent
-- name    : BianchiIX.basis_det_cons_normal_independent
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T05:36:40.152082+00:00
-- url     : https://prove2.me/theorems/b83e13be-a0a1-4c25-8cee-7d8a9117d1b0
-- title:
--   A contracted determinant is independent of the normalized transverse vector
-- statement:
--   Let $E$ be a real vector space with basis $b$ indexed by
--   $\{0,\ldots,n\}$, let $\ell:E\to\mathbb R$ be linear, and suppose
--   $\ell(X)=\ell(Y)=1$ and $\ell(v_i)=0$ for $0\leq i<n$. Then
--   $$\det_b(Y,v_0,\ldots,v_{n-1})=\det_b(X,v_0,\ldots,v_{n-1}).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/VolumeForms.lean#L22-L35

import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]

theorem BianchiIX.basis_det_cons_normal_independent {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℝ E)
    {l : E →ₗ[ℝ] ℝ} {X Y : E} {v : Fin n → E}
    (hX : l X = 1) (hY : l Y = 1) (hv : ∀ i, l (v i) = 0) :
    b.det (Fin.cons Y v) = b.det (Fin.cons X v) := by sorry
