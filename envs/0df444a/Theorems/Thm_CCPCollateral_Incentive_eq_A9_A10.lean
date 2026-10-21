-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_eq_A9_A10
-- name    : CCPCollateral.Incentive.eq_A9_A10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:14.974306+00:00
-- url     : https://prove2.me/theorems/d2e79956-bfba-439e-b58a-7e6e6db28921
-- title:
--   (A9)–(A10), proof of Proposition 2, p. 47 — left and right derivatives of F̂ at a kink I_l are H(l + 1) − 1 and H(l) − 1
-- statement:
--   Under the standing assumptions, let $0<I_l<\hat I(0)$ be a kink, $N\hat F(I_l)=l(D-I_l)$ with $1\le l\le N-1$. Then $\hat F$ has one-sided derivatives at $I_l$:
--   $$\frac{d\hat F(I_l-\epsilon)}{dI}+1=H(l+1),\qquad \frac{d\hat F(I_l+\epsilon)}{dI}+1=H(l),$$
--   i.e. the left derivative is $H(l+1)-1$ and the right derivative is $H(l)-1$, with $H$ as in (A7).
--
--   Together with (A11) this shows that $\hat F$ is convex at every kink.
--
--   **Formalization Note** The one-sided derivatives are derivatives within $(-\infty,I_l]$ and $[I_l,\infty)$.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 2, (A9)–(A10), p. 47

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- (A9)–(A10), proof of Proposition 2, Step 2 (p. 47): at an interior kink `I_l`
(`N F̂(I_l) = l (D − I_l)`, `1 ≤ l ≤ N − 1`), the left derivative of `F̂` is `H(l + 1) − 1` and the
right derivative is `H(l) − 1`. -/
theorem eq_A9_A10 (m : Params) (hm : Standing m) (I : ℝ) (hI : I ∈ Set.Ioo 0 m.Ihat0) (l : ℕ)
    (hl1 : 1 ≤ l) (hlN : l ≤ m.N - 1) (hkink : (m.N : ℝ) * m.Fhat I = l * (m.D - I)) :
    HasDerivWithinAt m.Fhat (m.H (l + 1) - 1) (Set.Iic I) I ∧
      HasDerivWithinAt m.Fhat (m.H l - 1) (Set.Ici I) I := by sorry

end CCPCollateral.Incentive
