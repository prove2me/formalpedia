-- Prove2me | Theorems.Thm_CompositeLB_DetSC_xstar_closed_form
-- name    : CompositeLB.DetSC.xstar_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:58.070979+00:00
-- url     : https://prove2.me/theorems/a5e4fd45-3f89-4c98-8a56-9fa4219590da
-- title:
--   Appendix B.4, p. 17 — the minimizer x* and its value
-- statement:
--   Let $m\ge2$, $k\ge1$, $0<\lambda<1$, and let $v_0,\ldots,v_k$ be orthonormal. At every $1\le r\le k$, let the binary indicators $\delta_{i,r}$ sum to $\lfloor m/2\rfloor$. Define $Q=(\lfloor m/2\rfloor/m)(1/\lambda-1)+1$, $q=(\sqrt Q-1)/(\sqrt Q+1)$, and choose $\zeta=1-q$. Then the global minimum of their averaged objective $F$ is attained at $x^*=C\sum_{r=0}^k q^{r+1}v_r$, with
--
--   $$F(x^*)=-\frac{\lambda C^2}{8}(\sqrt Q-1)^2.$$
--
--   This gives the optimum and fixes the initial suboptimality used to calibrate the hard instance.
--
--   **Formalization Note** The minimum is a pointwise inequality over all of $\mathbb R^d$. The rendered PDF has no extra factor of $1/2$ in $F(x^*)$; the flattened text extraction does.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.4, p. 17, displays defining q, x* and F(x*)

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

namespace CompositeLB.DetSC

/-- Appendix B.4, p. 17: the exact minimizer and its objective value. -/
theorem xstar_closed_form {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (lam C zeta : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1)
    (v : ℕ → CompositeLB.DetLip.E d)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (delta : Fin m → ℕ → ℝ)
    (hdelta : ∀ i r, delta i r = 0 ∨ delta i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, delta i r = ((m / 2 : ℕ) : ℝ))
    (hzeta : zeta = 1 - qq m lam) :
    (∀ y : CompositeLB.DetLip.E d,
      hardAvg lam C zeta k v delta (hardXstar m lam C k v) ≤
        hardAvg lam C zeta k v delta y) ∧
      hardAvg lam C zeta k v delta (hardXstar m lam C k v) =
        -(lam * C ^ 2 / 8) * (Real.sqrt (bigQ m lam) - 1) ^ 2 := by sorry

end CompositeLB.DetSC
