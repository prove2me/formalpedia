-- Prove2me | Theorems.Thm_BlockchainTFM_aux_payment_lower_bound
-- name    : BlockchainTFM.aux_payment_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:35.811088+00:00
-- url     : https://prove2.me/theorems/2a43b7e8-f0c0-4173-8844-45e221547b79
-- title:
--   (EC.134)–(EC.135): $a_ip_i\ge\frac{g(\lambda_0)}{2e}\cdot\frac kn\,b_i^2$ in the auxiliary mechanism
-- statement:
--   Fix $\lambda_0>e/(e-1)$, a block size $k\ge1$ and $n\ge\max\{\lambda_0k,30\}$, and let $M=(\mathbf a,\mathbf p,0)$ be the auxiliary mechanism for block size $k$ with $m=m_\#(\lambda_0)$: $\mathbf a$ is Mechanism 3's allocation and $\mathbf p$ its dominant association. For every user $i$ and every bid vector $\mathbf b\in[0,1]^n$,
--   $$a_i(b_i,\mathbf b_{-i})\,p_i(b_i,\mathbf b_{-i})=\int_0^{b_i}t\,\frac{\partial a_i(t,\mathbf b_{-i})}{\partial t}\,dt\ \ge\ \frac{g(\lambda_0)}{2e}\cdot\frac kn\,b_i^2.$$
--
--   The expected payment of every user in the auxiliary mechanism is thus at least quadratic in her bid. This is what lets the variation term with $h\le g(\lambda_0)\,2kc_\rho(n-1)/(en^2)$ keep Mechanism 3 individually rational and budget feasible (Theorem 4 (B)) and bounds the cost of fake bids (Theorem 4 (C)).
--
--   **Formalization Note** The expected payment is written in the equivalent form (EC.137), $a_ip_i=a_ib_i-\int_0^{b_i}a_i(t,\mathbf b_{-i})\,dt$.
--
--   Differences from the source:
--   - reading: g(λ) in (EC.135) → g(λ₀); reason: the derivation replaces n/k by λ₀ at (EC.130), and (EC.136) uses g(λ₀)
--   - encoding: a_i p_i = ∫₀^{b_i} t ∂a_i/∂t dt (EC.134) → a_i b_i − ∫₀^{b_i} a_i(t, b_{−i}) dt (EC.137 form, via auxMech); reason: equal by integration by parts, as the paper notes at (EC.137)
--   - encoding: users 1,…,n; b_{−i}; bids and values in [0,1] → Fin n; a vector b ∈ [0,1]ⁿ whose i-th entry is overwritten (Function.update); bids, values and deviations in Set.Icc 0 1; reason: Lean convention; same instances
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Appendix EC.4.4.2, (EC.134)–(EC.135), p.ec23 (with (EC.137) p.ec24)

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Mechanism3
import Definitions.Def_BlockchainTFM_Constants

namespace BlockchainTFM

/-- **Lower bound on the auxiliary payment**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7,
Appendix EC.4.4.2, (EC.134)–(EC.135), p.ec23. Fix `λ₀ > e/(e−1)`, a block size `k ≥ 1` and
`n ≥ max{λ₀k, 30}` users, and set `m = m_#(λ₀)`. In the auxiliary mechanism for block size `k`
(allocation `a` of Mechanism 3, payment the dominant association of `a`), for every user `i`
and every bid vector `b ∈ [0,1]ⁿ`,
`a_i(b_i, b_{-i}) p_i(b_i, b_{-i}) = ∫₀^{b_i} t ∂a_i(t, b_{-i})/∂t dt ≥ (g(λ₀)/(2e)) (k/n) b_i²`.

**Formalization Note.** The auxiliary payment is written in the equivalent form (EC.137),
`a_i p_i = a_i b_i − ∫₀^{b_i} a_i(t, b_{-i}) dt` (`auxMech`). The paper's (EC.135) writes
`g(λ)`; the derivation passes from `n/k` to `λ₀` at (EC.130), so the constant is `g(λ₀)`. -/
theorem aux_payment_lower_bound (lam0 : ℝ) (hlam0 : Real.exp 1 / (Real.exp 1 - 1) < lam0)
    (k n : ℕ) (hk : 1 ≤ k) (hn : max (lam0 * k) 30 ≤ (n : ℝ))
    (b : Fin n → ℝ) (hb : b ∈ bidBox n) (i : Fin n) :
    gConst lam0 / (2 * Real.exp 1) * ((k : ℝ) / n) * b i ^ 2 ≤
      (auxMech n k (mSharp lam0)).alloc b i * (auxMech n k (mSharp lam0)).pay b i := by sorry

end BlockchainTFM
