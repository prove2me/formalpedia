-- Prove2me | Theorems.Thm_CubeSampling_proposition_3_3
-- name    : CubeSampling.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:19:36.167692+00:00
-- url     : https://prove2.me/theorems/6c2b9072-07dd-45e4-a415-683c03fa257d
-- title:
--   Proposition 3.3 — one-dimensional clipping: $|\log T_{d,k}(\eta) - \Lambda_{d,k}| \le C k^{1/3}$
-- statement:
--   **Proposition 3.3.** Fix $q_0 \in (0, 1/2)$ and $\eta \in (0,1)$. There is $C_{\eta,q_0}$ such that for all integers $1 \le k \le q_0 d$,
--   $$
--   \bigl|\log T_{d,k}(\eta) - \Lambda_{d,k}\bigr| \le C_{\eta,q_0}\, k^{1/3},
--   $$
--   where $T_{d,k}(\eta) = \sup_{h \in P_{d,k},\,\mathbb E[h^2]=1} \inf\{B > 0 : \mathbb E[h^2 \wedge B] \ge \eta\}$.
--
--   The clipping level controls the sample size of stable sampling (Proposition 3.4) and is the first step of the upper bound in Theorem 1.5.
--
--   Differences from the source: none.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Proposition 3.3, p.13

import Mathlib
import Definitions.Def_CubeSampling_clipT
import Definitions.Def_CubeSampling_Lambda

namespace CubeSampling

/-- Proposition 3.3 (one-dimensional clipping) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Proposition 3.3, p.13): fix `q₀ ∈ (0, 1/2)` and
`η ∈ (0, 1)`; there is `C_{η,q₀}` such that `|log T_{d,k}(η) − Λ_{d,k}| ≤ C_{η,q₀} k^{1/3}` for all integers
`1 ≤ k ≤ q₀ d`. -/
theorem proposition_3_3 (q₀ : ℝ) (hq₀ : 0 < q₀) (hq₀' : q₀ < 1 / 2) (η : ℝ) (hη : 0 < η)
    (hη' : η < 1) :
    ∃ C : ℝ, ∀ d k : ℕ, 1 ≤ k → (k : ℝ) ≤ q₀ * d →
      |Real.log (clipT d k η) - Lambda d k| ≤ C * (k : ℝ) ^ ((1 : ℝ) / 3) := by sorry

end CubeSampling
