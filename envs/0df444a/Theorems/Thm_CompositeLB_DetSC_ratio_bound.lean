-- Prove2me | Theorems.Thm_CompositeLB_DetSC_ratio_bound
-- name    : CompositeLB.DetSC.ratio_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:26:06.787847+00:00
-- url     : https://prove2.me/theorems/f7155a6f-fc87-4cb4-b3bc-6f092a36fb36
-- title:
--   Appendix B.4, p. 17 — ratio bound for a point orthogonal to unseen directions
-- statement:
--   Under the same orthonormal chain, binary indicator, and $\zeta=1-q$ conditions as the minimizer formula, let $C\ne0$, $t\le k$, and let $x$ be orthogonal to $v_t,\ldots,v_k$. With $x^*=C\sum_{r=0}^kq^{r+1}v_r$ and $F$ the averaged objective,
--
--   $$\frac{F(x)-F(x^*)}{F(0)-F(x^*)}\ge\frac{q^{2t}-q^{2k+2}}{\sqrt Q},\qquad Q=\frac{\lfloor m/2\rfloor}{m}(1/\lambda-1)+1.$$
--
--   The ratio compares current error with initial error while the later directions are unseen.
--
--   **Formalization Note** Orthogonality is the equivalent form of the page's condition that an iterate lies in the span of earlier directions. The nonzero $C$ makes the denominator positive. The theorem includes $t=0$, which the displayed algebra permits.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.4, p. 17, final displayed ratio chain

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

namespace CompositeLB.DetSC

/-- Appendix B.4, p. 17: the objective gap of a point orthogonal to unseen directions. -/
theorem ratio_bound {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (lam C zeta : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1) (hC : C ≠ 0)
    (v : ℕ → CompositeLB.DetLip.E d)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (delta : Fin m → ℕ → ℝ)
    (hdelta : ∀ i r, delta i r = 0 ∨ delta i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, delta i r = ((m / 2 : ℕ) : ℝ))
    (hzeta : zeta = 1 - qq m lam)
    (t : ℕ) (ht : t ≤ k) (x : CompositeLB.DetLip.E d)
    (hx : ∀ r, t ≤ r → r ≤ k → inner ℝ x (v r) = 0) :
    (hardAvg lam C zeta k v delta x -
        hardAvg lam C zeta k v delta (hardXstar m lam C k v)) /
      (hardAvg lam C zeta k v delta 0 -
        hardAvg lam C zeta k v delta (hardXstar m lam C k v)) ≥
      ((qq m lam) ^ (2 * t) - (qq m lam) ^ (2 * k + 2)) /
        Real.sqrt (bigQ m lam) := by sorry

end CompositeLB.DetSC
