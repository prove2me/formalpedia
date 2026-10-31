-- Prove2me | Theorems.Thm_CryptoMiningMFG_eq_2_6_maximizer
-- name    : CryptoMiningMFG.eq_2_6_maximizer
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:57:34.21839+00:00
-- url     : https://prove2.me/theorems/9d3de2f7-1ecd-4a28-918c-e64c8490f141
-- title:
--   Eq. (2.6): the optimal hash rate is the unique maximizer of the Hamiltonian
-- statement:
--   Let $\mathcal K,c,M,\bar\alpha>0$ and let $p>0$, $q>0$ stand for $\partial_x v$ and $\Delta v$. Consider the Hamiltonian of the HJB equation (2.5),
--
--   $$
--   H(\alpha)=-c\,\alpha\,p+\mathcal K\frac{\alpha}{\alpha+M\bar\alpha}\,q,\qquad \alpha\ge0,
--   $$
--
--   and the candidate
--
--   $$
--   \alpha^*=\begin{cases}-M\bar\alpha+\sqrt{\dfrac{\mathcal K M\bar\alpha\,q}{c\,p}}, & \bar\alpha<\dfrac{\mathcal K q}{M c p},\\[6pt] 0, & \text{otherwise}.\end{cases}
--   $$
--
--   Then $\alpha^*\ge0$, and $H(\alpha)<H(\alpha^*)$ for every $\alpha\ge0$ with $\alpha\neq\alpha^*$: the formula (2.6) is the unique optimal hash rate.
--
--   This is the pointwise optimization behind the feedback (2.6) and, through it, behind the explicit equilibrium.
--
--   **Formalization Note** At $\alpha=0$ the term $\mathcal K\alpha/(\alpha+M\bar\alpha)$ is $0$, the $\alpha=0$ branch of the intensity (2.2).
--
--   Differences from the source:
--   - generalization: (2.6) is stated with ∂ₓv(t, x; ᾱ) and Δv(t, x; ᾱ) of the value function, both positive by Lemma 2.1 → the maximizer property is stated for arbitrary p > 0, q > 0 in place of ∂ₓv and Δv; reason: the page's case is the instance p = ∂ₓv, q = Δv
--   - reading: "the optimal hash rate is given by" (2.6) → (2.6) is nonnegative and strictly beats every other α ≥ 0 in the Hamiltonian of (2.5); reason: "optimal" means the maximizer of the supremum in (2.5); uniqueness is part of "the" optimal rate
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, eq. (2.6) p.11 (with the Hamiltonian of (2.5), p.10)

import Mathlib

namespace CryptoMiningMFG

/-- **The optimal hash rate (2.6) maximizes the Hamiltonian of (2.5).** Li, Reppen, Sircar,
*A Mean Field Games Model for Cryptocurrency Mining*, arXiv:1912.01952v2, eq. (2.6), p.11.

Let `𝒦, c, M, ᾱ > 0` and let `p > 0`, `q > 0` play the roles of `∂ₓv` and `Δv`. The function
`H(α) = −c α p + 𝒦 α / (α + M ᾱ) · q` on `α ≥ 0` (the expression inside the supremum of the HJB
equation (2.5), p.10) has the unique maximizer
`α* = −M ᾱ + √(𝒦 M ᾱ q / (c p))` if `ᾱ < 𝒦 q / (M c p)`, and `α* = 0` otherwise:
`α* ≥ 0`, and every other `α ≥ 0` gives a strictly smaller value.

**Formalization Note.** At `α = 0` the intensity `𝒦 α / (α + M ᾱ)` is `0`, which is the `α = 0`
branch of (2.2). -/
theorem eq_2_6_maximizer (K c M abar p q : ℝ) (hK : 0 < K) (hc : 0 < c) (hM : 0 < M)
    (habar : 0 < abar) (hp : 0 < p) (hq : 0 < q) :
    let H : ℝ → ℝ := fun α => -c * α * p + K * α / (α + M * abar) * q
    let αstar : ℝ := if abar < K * q / (M * c * p) then
      -M * abar + Real.sqrt (K * M * abar * q / (c * p)) else 0
    0 ≤ αstar ∧ ∀ α : ℝ, 0 ≤ α → α ≠ αstar → H α < H αstar := by sorry

end CryptoMiningMFG
