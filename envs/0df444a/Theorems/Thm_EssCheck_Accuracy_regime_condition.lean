-- Prove2me | Theorems.Thm_EssCheck_Accuracy_regime_condition
-- name    : EssCheck.Accuracy.regime_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:08.167058+00:00
-- url     : https://prove2.me/theorems/d7028d5d-e582-46a6-b45d-41908c127eb9
-- title:
--   Equation (4) — hybrid licensing regime
-- statement:
--   Fix an interior expected research effort $\hat x$, accuracy $\beta\in[0,1]$, and a commercial-value state $i$. The licensing equilibrium in that state is hybrid exactly when the cross-multiplied form of equation (4) holds:
--   $$\hat x p_i^H l_i\le(1-\beta)(1-\hat x)p_i^0(\bar\alpha v_i-l_i).$$
--   When $p_i^0>0$, this is also equivalent to the ratio form printed in the paper:
--   $$\frac{(1-\beta)(1-\hat x)}{\hat x}\ge\frac{p_i^H l_i}{p_i^0(\bar\alpha v_i-l_i)}.$$
--   This identifies the hybrid states used in the revenue and welfare formulas.
--
--   **Formalization Note** The cross-multiplied condition covers states with $p_i^0=0$ without giving a denominator a spurious value.
-- source:
--   Schuett & Wipusanawan, Essentiality Checks for Standard Essential Patents, TILEC Discussion Paper DP 2023-21 (Dec. 2023; SSRN 4688864), p. 18 (PDF 19), equation (4) and preceding paragraph

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

namespace EssCheck.Accuracy

theorem regime_condition {n : ℕ} (M : Model n) (hS : M.Standing)
    (β xh : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hx0 : 0 < xh) (hx1 : xh < 1) (i : Fin n) :
    (IsHybrid M β xh i ↔
      xh * M.pH i * M.l i ≤ (1 - β) * (1 - xh) * M.p0 i *
        (M.αbar * M.v i - M.l i)) ∧
    (0 < M.p0 i →
      (IsHybrid M β xh i ↔
        M.pH i * M.l i / (M.p0 i * (M.αbar * M.v i - M.l i)) ≤
          (1 - β) * (1 - xh) / xh)) := by sorry

end EssCheck.Accuracy
