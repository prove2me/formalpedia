-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_eq_A7
-- name    : CCPCollateral.Incentive.eq_A7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:17.376017+00:00
-- url     : https://prove2.me/theorems/e9bd2b6e-aaa3-4190-b607-c0247cb0ee98
-- title:
--   (A7), proof of Proposition 2, p. 46 — dF̂/dI + 1 = H(⌈N F̂/(D − I)⌉) off the kinks; 0 < H(l) < 1 for l ≤ N − 1
-- statement:
--   Under the standing assumptions, let
--   $$H(l)=\frac{\alpha\,\mathbb E^s[\mathbb 1_{\mathcal N_d\ge l}]}{\mathbb E^s\!\left[\frac{N}{N-\mathcal N_d}\right]-\mathcal P+\alpha\,\mathbb E^s\!\left[\frac{N}{N-\mathcal N_d}\mathbb 1_{\mathcal N_d\ge l}\right]}.$$
--   1. If $0<I<\hat I(0)$ and $l$ is a natural number with $l-1<N\hat F(I)/(D-I)<l$ (so $\lceil N\hat F(I)/(D-I)\rceil=l$ and $I$ is not a kink), then $\hat F$ is differentiable at $I$ and
--   $$\frac{d\hat F(I)}{dI}+1=H(l).$$
--   2. For every $l\le N-1$, $0<H(l)<1$.
--
--   Hence $\hat F$ has slope in $(-1,0)$ wherever $\lceil N\hat F(I)/(D-I)\rceil\le N-1$.
--
--   **Formalization Note** The page states "$\in(0,1)$" for $l=\lceil NF/(D-I)\rceil$ without a bound on $l$. At $l=N$ (the prefunded default fund covers the shortfall of all $N-1$ other members) the numerator vanishes and the slope is exactly $-1$; part 2 is therefore stated for $l\le N-1$, the range the page's kink set presupposes.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 2, (A6)–(A7), p. 46

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- (A7), proof of Proposition 2, Step 2 (p. 46): off the kinks, with `l = ⌈N F̂(I)/(D − I)⌉`,
`dF̂/dI + 1 = H(l)`; and `0 < H(l) < 1` for `l ≤ N − 1` (corrected range). -/
theorem eq_A7 (m : Params) (hm : Standing m) :
    (∀ I ∈ Set.Ioo 0 m.Ihat0, ∀ l : ℕ,
      (l : ℝ) - 1 < (m.N : ℝ) * m.Fhat I / (m.D - I) →
      (m.N : ℝ) * m.Fhat I / (m.D - I) < l →
        HasDerivAt m.Fhat (m.H l - 1) I) ∧
    (∀ l : ℕ, l ≤ m.N - 1 → 0 < m.H l ∧ m.H l < 1) := by sorry

end CCPCollateral.Incentive
