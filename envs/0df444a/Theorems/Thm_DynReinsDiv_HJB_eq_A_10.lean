-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_eq_A_10
-- name    : DynReinsDiv.HJB.eq_A_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:30.317464+00:00
-- url     : https://prove2.me/theorems/0ca5c978-083d-4da2-b5c5-1714eafba4fb
-- title:
--   (A.10) — 𝓛v = A(−v_xx/v_x)v_xx + B(−v_xx/v_x)v_x − γv_x − cv when v_x > 0
-- statement:
--   Let $\mathcal L$ be the operator (3.2) of a model and $A$, $B$ the functions (A.5), (A.6). For all real numbers $q$, $w$ and every $p>0$,
--   $$\mathcal L(q,p,w)=A\Big(-\frac qp\Big)q+B\Big(-\frac qp\Big)p-\gamma p-cw .$$
--   Read with $q=v_{xx}$, $p=v_x$, $w=v$ this is (A.10): the supremum over retained-loss functions in (3.2) is computed in closed form, attained by $h^*(z)=\min\{z,\,-v_x/v_{xx}\}$ when $v_{xx}<0$ and by full retention otherwise. It turns the variational inequality (3.1) into one for a fully nonlinear operator with explicit coefficients.
--
--   **Formalization Note** The paper states (A.10) under $v_x\ge1$ (p. 21, "Notice $v_x\ge1$ in (3.1)"); the statement here asks only $v_x>0$, which is what the computation uses.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, pp. 21–22, (A.2)–(A.6) and (A.10)

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model

namespace DynReinsDiv.HJB

theorem eq_A_10 (M : Model) (q p w : ℝ) (hp : 0 < p) :
    M.Lop q p w = M.A (-q / p) * q + M.B (-q / p) * p - M.γ * p - M.c * w := by sorry

end DynReinsDiv.HJB
