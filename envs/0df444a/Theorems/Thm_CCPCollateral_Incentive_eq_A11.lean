-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_eq_A11
-- name    : CCPCollateral.Incentive.eq_A11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:14.499777+00:00
-- url     : https://prove2.me/theorems/b93b58b9-e4b6-4ce9-831f-db4b1e46f465
-- title:
--   (A11), proof of Proposition 2, p. 47 — the right slope of F̂ exceeds its left slope at every interior kink
-- statement:
--   At an interior kink $I_l$ with $N\hat F(I_l)=l(D-I_l)$ and $1\le l\le N-1$, equations (A9)–(A10) give the one-sided slopes $H(l+1)-1$ and $H(l)-1$. Equation (A11) states their strict order:
--   $$\frac{d\hat F(I_l+\epsilon)}{dI}>\frac{d\hat F(I_l-\epsilon)}{dI}.$$
--   Thus $\hat F$ bends upward at every interior kink.
--
--   **Formalization Note** The endpoint $I_0=\hat I(0)$ has no right-hand interval in the cutoff's domain. The page's inequality uses a positive probability of exactly $l$ defaults, which holds for $l\le N-1$.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 2, (A11) and footnote 26, p. 47

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- (A11), proof of Proposition 2, Step 2 (p. 47): at an interior kink `I_l`, the right
one-sided derivative `H(l) − 1` strictly exceeds the left derivative `H(l + 1) − 1`. -/
theorem eq_A11 (m : Params) (hm : Standing m) :
    ∀ I ∈ Set.Ioo 0 m.Ihat0, ∀ l : ℕ, 1 ≤ l → l ≤ m.N - 1 →
      (m.N : ℝ) * m.Fhat I = l * (m.D - I) →
      HasDerivWithinAt m.Fhat (m.H (l + 1) - 1) (Set.Iic I) I ∧
      HasDerivWithinAt m.Fhat (m.H l - 1) (Set.Ici I) I ∧
      m.H (l + 1) - 1 < m.H l - 1 := by sorry

end CCPCollateral.Incentive
