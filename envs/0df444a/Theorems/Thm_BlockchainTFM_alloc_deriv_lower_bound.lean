-- Prove2me | Theorems.Thm_BlockchainTFM_alloc_deriv_lower_bound
-- name    : BlockchainTFM.alloc_deriv_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:38.314367+00:00
-- url     : https://prove2.me/theorems/57b1ad61-f3d8-4325-b9d8-3286d88443bd
-- title:
--   (EC.131): $\partial a_i/\partial b_i\ge \frac kn\,f(\lambda_0)e^{-e/(0.9\lambda_0-1)}=\frac kn\,g(\lambda_0)/e$
-- statement:
--   Fix $\lambda_0>e/(e-1)$, a block size $k\ge1$ and a number of users $n\ge\max\{\lambda_0k,30\}$, and run Mechanism 3's allocation with $m=m_\#(\lambda_0)$. For every user $i$, every $\mathbf b_{-i}\in[0,1]^{n-1}$ and every own bid $t\in[0,1]$,
--   $$\frac{\partial a_i(t,\mathbf b_{-i})}{\partial t}\ \ge\ \frac kn\,f(\lambda_0)\,e^{-\frac{e}{0.9\lambda_0-1}}\ =\ \frac kn\cdot\frac{g(\lambda_0)}{e},$$
--   where $f(\lambda_0)=m\,D(m,\lambda_0)/e^m$ with $D(m,\lambda)=\max\{1-\sqrt{\ln\frac{\lambda}{\lambda-1}},\,1-e\ln\frac{\lambda}{\lambda-1}\}$, and $g$ is the constant of Theorem 4.
--
--   The bound says the allocation increases at a rate of order $k/n$ in the own bid, uniformly in the other bids. Integrated against $t$ it gives the payment lower bound (EC.135), which drives UIR, BF and the U-SP estimate of Theorem 4.
--
--   **Formalization Note** The allocation is a smooth function of the own bid on all of $\mathbb R$, so the derivative is the ordinary derivative.
--
--   Differences from the source:
--   - encoding: f(λ₀) e^{−e/(0.9λ₀−1)} with f(λ₀) = m D(m,λ₀)/e^m → gConst λ₀ / e; reason: (EC.132) defines g = e f e^{−e/(0.9λ−1)}, which is Theorem 4's g; same number
--   - encoding: users 1,…,n; b_{−i}; bids and values in [0,1] → Fin n; a vector b ∈ [0,1]ⁿ whose i-th entry is overwritten (Function.update); bids, values and deviations in Set.Icc 0 1; reason: Lean convention; same instances
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Appendix EC.4.4.2, (EC.127)–(EC.132), p.ec23 (with (EC.115)–(EC.116) p.ec21 and (EC.123) p.ec22)

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Mechanism3
import Definitions.Def_BlockchainTFM_Constants

namespace BlockchainTFM

/-- **Lower bound on `∂a_i/∂b_i`**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7, Appendix
EC.4.4.2, (EC.127)–(EC.132), p.ec23. Fix `λ₀ > e/(e−1)`, a block size `k ≥ 1` and
`n ≥ max{λ₀k, 30}` users, and set `m = m_#(λ₀)`. For Mechanism 3's allocation rule, every user
`i`, every `b_{-i} ∈ [0,1]^{n−1}` and every own bid `t ∈ [0,1]`,
`∂a_i(t, b_{-i})/∂t ≥ (k/n) · f(λ₀) e^{−e/(0.9λ₀−1)} = (k/n) · g(λ₀)/e`.

**Formalization Note.** The paper writes the bound with `f(λ₀) = m D(m, λ₀)/e^m`, where
`D(m, λ) = max{1 − √(ln(λ/(λ−1))), 1 − e ln(λ/(λ−1))}` ((EC.116), (EC.123)); by (EC.132),
`f(λ₀) e^{−e/(0.9λ₀−1)} = g(λ₀)/e` with `g` of Theorem 4 (`gConst`). The allocation is smooth
in the own bid on all of `ℝ`, so the derivative is the ordinary one (`deriv`). -/
theorem alloc_deriv_lower_bound (lam0 : ℝ) (hlam0 : Real.exp 1 / (Real.exp 1 - 1) < lam0)
    (k n : ℕ) (hk : 1 ≤ k) (hn : max (lam0 * k) 30 ≤ (n : ℝ))
    (b : Fin n → ℝ) (hb : b ∈ bidBox n) (i : Fin n) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((k : ℝ) / n) * (gConst lam0 / Real.exp 1) ≤
      deriv (fun s => alloc3 k (mSharp lam0) (Function.update b i s) i) t := by sorry

end BlockchainTFM
