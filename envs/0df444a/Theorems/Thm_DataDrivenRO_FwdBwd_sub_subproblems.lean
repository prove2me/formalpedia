-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_sub_subproblems
-- name    : DataDrivenRO.FwdBwd.sub_subproblems
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:02:23.225025+00:00
-- url     : https://prove2.me/theorems/1d0472fc-3812-4db5-b68f-9992557a399a
-- title:
--   Proof of Theorem 6, p. ec5 — the three one-dimensional sub-subproblems and their optimal values
-- statement:
--   Let $m_b\le m_f$, $\bar\sigma_f,\bar\sigma_b>0$, $\lambda>0$ and $v$ be real numbers. Then:
--
--   1. $\displaystyle\max_{m_b\le y\le m_f} vy = \begin{cases} m_f v & v\ge 0,\\ m_b v & v<0;\end{cases}$
--   2. $\displaystyle\max_{y\ge0}\ vy - \lambda\frac{y^2}{2\bar\sigma_f^2} = \begin{cases}\dfrac{v^2\bar\sigma_f^2}{2\lambda} & v\ge0,\\ 0 & v<0;\end{cases}$
--   3. $\displaystyle\max_{y\ge0}\ -vy - \lambda\frac{y^2}{2\bar\sigma_b^2} = \begin{cases}\dfrac{v^2\bar\sigma_b^2}{2\lambda} & v\le0,\\ 0 & v>0.\end{cases}$
--
--   Each maximum is attained. In the proof of Theorem 6 the inner maximisation of the Lagrangian decouples by coordinate, and each coordinate's problem splits into these three.
--
--   **Formalization Note** The page prints the optimal values of the second and third problems as $v_i\bar\sigma^2/(2\lambda)$; the correct value, which the page's next display uses, is $v_i^2\bar\sigma^2/(2\lambda)$. The statement uses the corrected value.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem 6, p. ec5 (the three sub-subproblems)

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

namespace DataDrivenRO.FwdBwd

theorem sub_subproblems (mb mf σf σb lam v : ℝ) (hm : mb ≤ mf) (hσf : 0 < σf) (hσb : 0 < σb)
    (hlam : 0 < lam) :
    IsGreatest ((fun y => v * y) '' Set.Icc mb mf) (if 0 ≤ v then mf * v else mb * v) ∧
    IsGreatest ((fun y => v * y - lam * (y ^ 2 / (2 * σf ^ 2))) '' Set.Ici 0)
      (if 0 ≤ v then v ^ 2 * σf ^ 2 / (2 * lam) else 0) ∧
    IsGreatest ((fun y => -v * y - lam * (y ^ 2 / (2 * σb ^ 2))) '' Set.Ici 0)
      (if v ≤ 0 then v ^ 2 * σb ^ 2 / (2 * lam) else 0) := by sorry

end DataDrivenRO.FwdBwd
