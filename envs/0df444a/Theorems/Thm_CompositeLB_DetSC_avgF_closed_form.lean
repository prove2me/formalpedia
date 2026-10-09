-- Prove2me | Theorems.Thm_CompositeLB_DetSC_avgF_closed_form
-- name    : CompositeLB.DetSC.avgF_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:25:28.230323+00:00
-- url     : https://prove2.me/theorems/8e11fe61-f0dd-448a-94f3-36d49d8640fc
-- title:
--   Appendix B.4, p. 17 — closed form of the average objective F
-- statement:
--   Let $m\ge2$, $k\ge1$, $\lambda>0$, and let the indicators $\delta_{i,r}$ take values in $\{0,1\}$. Suppose exactly $\lfloor m/2\rfloor$ components have $\delta_{i,r}=1$ at every $1\le r\le k$. For the Appendix B.4 components, the average is
--
--   $$F(x)=\frac{\lambda(Q-1)}8\left[\langle x,v_0\rangle^2-2C\langle x,v_0\rangle+\zeta\langle x,v_k\rangle^2+\sum_{r=1}^k\langle x,v_{r-1}-v_r\rangle^2\right]+\frac\lambda2\lVert x\rVert^2,$$
--
--   where $Q=(\lfloor m/2\rfloor/m)(1/\lambda-1)+1$. This identity exposes the quadratic whose minimizer and gap are analyzed next.
--
--   **Formalization Note** The directions need not be orthonormal for this averaging identity. Lean's m / 2 is the floor of $m/2$, and component indices start at zero.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.4, p. 17, display beginning ‘Since exactly’

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

namespace CompositeLB.DetSC

/-- Appendix B.4, p. 17: averaging the indicated components gives the displayed `F`. -/
theorem avgF_closed_form {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (lam C zeta : ℝ) (hlam : 0 < lam)
    (v : ℕ → CompositeLB.DetLip.E d) (delta : Fin m → ℕ → ℝ)
    (hdelta : ∀ i r, delta i r = 0 ∨ delta i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, delta i r = ((m / 2 : ℕ) : ℝ)) :
    ∀ x : CompositeLB.DetLip.E d,
      hardAvg lam C zeta k v delta x =
        lam * (bigQ m lam - 1) / 8 *
          ((inner ℝ x (v 0)) ^ 2 - 2 * C * inner ℝ x (v 0) +
            zeta * (inner ℝ x (v k)) ^ 2 +
            ∑ r ∈ Finset.Icc 1 k, (inner ℝ x (v (r - 1) - v r)) ^ 2) +
          lam / 2 * ‖x‖ ^ 2 := by sorry

end CompositeLB.DetSC
