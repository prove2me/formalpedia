-- Prove2me | Theorems.Thm_ConservativeAD_GradAE_remark_3d
-- name    : ConservativeAD.GradAE.remark_3d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:06.741487+00:00
-- url     : https://prove2.me/theorems/a40fb0bd-bf10-4408-a2ad-34d31569bde3
-- title:
--   Remark 3(d) — a potential of a conservative field is locally Lipschitz
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a conservative field and let $f:\mathbb R^p\to\mathbb R$ be a potential for $D$. Then $f$ is locally Lipschitz continuous: every point of $\mathbb R^p$ has a neighbourhood $U$ and a constant $L\ge0$ with
--
--   $$
--   |f(y)-f(x)|\le L\,|y-x|\qquad\text{for all }x,y\in U .
--   $$
--
--   This is why the paper writes "(locally Lipschitz continuous)" in parentheses in Theorem 1: the property is automatic for potentials. In the paper it rests on the local boundedness of conservative fields, quoted from Borwein, Moors and Wang.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), pp. 7–8, Remark 3(d)

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.GradAE

/-- Remark 3(d): a potential of a conservative field is locally Lipschitz continuous. -/
theorem remark_3d {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (hD : IsPotential D f) :
    LocallyLipschitz f := by sorry

end ConservativeAD.GradAE
