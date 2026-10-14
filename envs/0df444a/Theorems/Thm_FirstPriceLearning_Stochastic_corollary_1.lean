-- Prove2me | Theorems.Thm_FirstPriceLearning_Stochastic_corollary_1
-- name    : FirstPriceLearning.Stochastic.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:32.021965+00:00
-- url     : https://prove2.me/theorems/bc4602f1-2fa4-4eea-9509-68a01d6dfbc3
-- title:
--   Corollary 1 (iid values), p. 20 — Algorithm 3 on the quantized auction has expected regret O(√T log^2.5 T)
-- statement:
--   Run Algorithm 3 on the quantized first-price auction of §3.4 with $M=K=\lceil\sqrt T\rceil$ and $\delta=1/(2T)$, and bid the grid point it chooses for the clipped value (the induced policy). There is an absolute constant $C>0$ such that for every $T\ge2$, every value distribution $F$ on $[0,1]$ and every HOB distribution $G$ on $[0,1]$, with $v_1,\dots,v_T$ iid $F$ and $m_1,\dots,m_T$ iid $G$,
--
--   $$
--   \mathbb E[R_T(\pi;v)]\ \le\ C\sqrt T\,(\log T)^{5/2},
--   $$
--
--   where $R_T$ is the regret (3) of the original continuous-bid problem.
--
--   This is the policy behind Theorem 1.
--
--   **Formalization Note.** The paper's $M=K=T^{1/2}$ are rounded up to $\lceil\sqrt T\rceil$. The statement starts at $T\ge2$: at $T=1$ the bound is $0$ while the first bid is made without information. The quantized rewards $(c-a)\mathbb 1(m\le a)$ lie in $[-1,1]$ and Algorithm 3 runs on them as printed. The conclusion also asserts that the regret is integrable. The adversarial-value part of the corollary is not stated in this mission.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 20, Corollary 1 (i.i.d. part)

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_AuctionAlgorithm3

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- Corollary 1, iid part (p. 20): Algorithm 3 applied to the quantized first-price auction, with
`M = K = ⌈√T⌉` and `δ = 1/(2T)`, has expected regret `O(√T log^{2.5} T)` when the private values
are iid: there is an absolute constant `C > 0` such that for every `T ≥ 2`, every value law `F` and
every HOB law `G` on `[0, 1]`, the regret (3) of the induced policy is integrable and
`𝔼[R_T] ≤ C √T (log T)^{5/2}`. -/
theorem corollary_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T →
      ∀ (F μG : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure μG],
        F (Set.Icc (0 : ℝ) 1)ᶜ = 0 → μG (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        Integrable ((AuctionAlg3.policy T).regretOf μG) ((AuctionAlg3.policy T).jointLaw F μG) ∧
          (AuctionAlg3.policy T).expectedRegret F μG ≤
            C * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by sorry

end FirstPriceLearning.Stochastic
