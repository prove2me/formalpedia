-- Prove2me | Theorems.Thm_CheungIBOL_General_lemma_4
-- name    : CheungIBOL.General.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:11:08.137309+00:00
-- url     : https://prove2.me/theorems/b202b0af-5782-4b36-b467-f02bb346be0b
-- title:
--   Lemma 4 — guarantee for the perturbed potential
-- statement:
--   Let $b$ be any positive integer, $N\in\{0,\ldots,b\}$ any consumed-inventory value, and $\epsilon\ge0$ with no upper bound. For $\Psi_\epsilon(u)=(e^{(1+\epsilon)u}-1)/(e^{1+\epsilon}-1)$,
--   $$\frac{\Psi_\epsilon(\min\{b,N+1\}/b)-\Psi_\epsilon(N/b)}{1/b}
--    +(1+\epsilon)(1-\Psi_\epsilon(N/b))
--    \le\mathbf1\{N<b\}\frac{(b+1+\epsilon)(1-e^{-(1+\epsilon)/b})}{1-e^{-(1+\epsilon)}}.$$
--   This covers every resource and every time, including the depleted endpoint $N=b$, where both sides are zero. The right-hand coefficient is the reciprocal of the resource-specific factor in equation (14). The domain is the full integer inventory grid, not a continuous relaxation of it.
--
--   Differences from the source:
--   - encoding: any resource i, time t, and possible integer N_i^(t-1) in {0,...,b_i} → an arbitrary positive natural b and natural N with N <= b; reason: the formula depends only on these two integer values; the universal statement covers exactly the same inventory grid at every resource and time
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), Appendix A.2, PDF/printed pp. 41–42, Lemma 4 and equation (43), https://arxiv.org/abs/1810.05640v2

import Definitions.Def_CheungIBOL_General_Potential

namespace CheungIBOL.General

theorem lemma_4 (b : ℕ+) (N : ℕ) (hN : N ≤ (b : ℕ)) (ε : ℝ) (hε : 0 ≤ ε) :
    (potential ε (((min (b : ℕ) (N + 1) : ℕ) : ℝ) / (b : ℕ)) -
      potential ε ((N : ℝ) / (b : ℕ))) / (1 / (b : ℕ)) +
      (1 + ε) * (1 - potential ε ((N : ℝ) / (b : ℕ))) ≤
    (if N < (b : ℕ) then (1 : ℝ) else 0) *
      (((b : ℕ) + 1 + ε) * (1 - Real.exp (-(1 + ε) / (b : ℕ))) /
        (1 - Real.exp (-(1 + ε)))) := by sorry

end CheungIBOL.General
