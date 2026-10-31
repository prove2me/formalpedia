-- Prove2me | Theorems.Thm_CryptoMiningMFG_eq_2_7_max_hamiltonian
-- name    : CryptoMiningMFG.eq_2_7_max_hamiltonian
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:57:33.265407+00:00
-- url     : https://prove2.me/theorems/1b42faba-090a-43d5-b47c-01ffb86ff21f
-- title:
--   Eq. (2.7): the maximized Hamiltonian is $(\sqrt{Mc\bar\alpha p}-\sqrt{\mathcal K q})^2$
-- statement:
--   Let $\mathcal K,c,M,\bar\alpha>0$ and $p>0$, $q>0$ (the roles of $\partial_x v$ and $\Delta v$). The greatest value of
--
--   $$
--   H(\alpha)=-c\,\alpha\,p+\mathcal K\frac{\alpha}{\alpha+M\bar\alpha}\,q
--   $$
--
--   over $\alpha\ge0$ is
--
--   $$
--   \max_{\alpha\ge0}H(\alpha)=\begin{cases}\Big(\sqrt{Mc\bar\alpha\,p}-\sqrt{\mathcal K q}\Big)^2, & \bar\alpha<\dfrac{\mathcal K q}{M c p},\\[6pt] 0, & \text{otherwise}.\end{cases}
--   $$
--
--   This is what turns the HJB equation (2.5) into the simplified form (2.7).
--
--   Differences from the source:
--   - generalization: (2.7) is stated with ∂ₓv and Δv of the value function → the value of the supremum is stated for arbitrary p > 0, q > 0; reason: the page's case is the instance p = ∂ₓv, q = Δv
--   - reading: (2.7) is the PDE ∂ₜv + (√(Mcᾱ∂ₓv) − √(KΔv))² = 0 (resp. ∂ₜv = 0) obtained by plugging (2.6) into (2.5) → the identity sup_{α≥0} H(α) = (√(Mcᾱp) − √(Kq))² (resp. 0), stated as the greatest element of the image of [0, ∞); reason: this identity is the whole content of the simplification; the PDE for v rests on the paper's assumption that v is a classical solution of (2.5), which the mission does not make
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, eq. (2.7) p.11 ("we simplify the HJB equation (2.5) by plugging in (2.6)")

import Mathlib

namespace CryptoMiningMFG

/-- **The maximized Hamiltonian (2.7).** Li, Reppen, Sircar, *A Mean Field Games Model for
Cryptocurrency Mining*, arXiv:1912.01952v2, eq. (2.7), p.11 ("we simplify the HJB equation (2.5)
by plugging in (2.6)").

Let `𝒦, c, M, ᾱ > 0` and `p > 0`, `q > 0` (the roles of `∂ₓv` and `Δv`). The greatest value of
`H(α) = −c α p + 𝒦 α / (α + M ᾱ) · q` over `α ≥ 0` is
`(√(M c ᾱ p) − √(𝒦 q))²` if `ᾱ < 𝒦 q / (M c p)`, and `0` otherwise. -/
theorem eq_2_7_max_hamiltonian (K c M abar p q : ℝ) (hK : 0 < K) (hc : 0 < c) (hM : 0 < M)
    (habar : 0 < abar) (hp : 0 < p) (hq : 0 < q) :
    IsGreatest ((fun α : ℝ => -c * α * p + K * α / (α + M * abar) * q) '' Set.Ici 0)
      (if abar < K * q / (M * c * p) then
        (Real.sqrt (M * c * abar * p) - Real.sqrt (K * q)) ^ 2 else 0) := by sorry

end CryptoMiningMFG
