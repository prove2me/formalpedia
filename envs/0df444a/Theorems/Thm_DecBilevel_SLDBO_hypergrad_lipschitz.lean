-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_hypergrad_lipschitz
-- name    : DecBilevel.SLDBO.hypergrad_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:49.368836+00:00
-- url     : https://prove2.me/theorems/7f81e964-2180-4d52-9fd1-6b199b88f8e5
-- title:
--   Proof of Lemma A.8, p. 19 — ∇Φ is L_Φ-Lipschitz, with L_Φ = L₁(1 + L_{f,1}/σ)²
-- statement:
--   Let $F_i,f_i$ ($n\ge1$) satisfy Assumption 2.1 and let $y^*(x)$ minimize $f(x,\cdot)$ for every $x$. With $L_1=L_{F,1}+L_{f,2}r_v$ and
--   $$L_\Phi=L_1\Big(1+\frac{L_{f,1}}\sigma\Big)^2,$$
--   the hypergradient (7) satisfies, for all $x,x'\in\mathbb R^p$,
--   $$\|\nabla\Phi(x)-\nabla\Phi(x')\|\le L_\Phi\|x-x'\|.$$
--
--   This is the smoothness of $\Phi$ that the descent inequality (41) uses.
--
--   **Formalization Note.** The paper cites this from [12, Lemma 2.2] with $L_\Phi$ of (8), whose second term contains $L_{f,2}L_{F,0}^2/\sigma$. That term is not homogeneous in the scale of $F$ (every other term is linear in it), so it is a misprint; expanding $L_1(1+L_{f,1}/\sigma)^2$ gives (8) with $L_{F,0}^2$ replaced by $L_{F,0}$. The constant here is the corrected one. $\nabla\Phi$ is the formula `hypergrad`, which is the gradient of $\Phi$ by milestone (7).
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 19, proof of Lemma A.8 ('∇Φ(x) is LΦ-Lipschitz continuous'); LΦ from (8), p. 5, corrected

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem hypergrad_lipschitz {n p q : ℕ} (hn : 0 < n) (F f : Fin n → E p → E q → ℝ)
    (σ LF0 LF1 Lf1 Lf2 : ℝ) (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2)
    (ystar : E p → E q) (hystar : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x)) (x x' : E p) :
    ‖hypergrad F f ystar x - hypergrad F f ystar x'‖ ≤ LPhi σ LF0 LF1 Lf1 Lf2 * ‖x - x'‖ := by sorry

end DecBilevel.SLDBO
