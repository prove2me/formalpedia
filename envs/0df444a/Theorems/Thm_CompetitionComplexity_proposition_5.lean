-- Prove2me | Theorems.Thm_CompetitionComplexity_proposition_5
-- name    : CompetitionComplexity.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:32.53824+00:00
-- url     : https://prove2.me/theorems/456b0ae7-0fb9-41cd-8ccb-37dcedbe6e69
-- title:
--   Proposition 5 — (15)–(16) has a unique solution $y_\varepsilon$, strictly decreasing and invertible on $[0,\phi(\varepsilon)]$, with $y_\varepsilon(\phi(\varepsilon))=0$
-- statement:
--   Let $\varepsilon>0$ and consider
--   $$
--   y'(t)=y(t)\bigl(\log y(t)-1\bigr)-\varepsilon\quad(t\in(0,\phi(\varepsilon))),\qquad y(0)=1,
--   $$
--   with $y$ extended continuously to $t=\phi(\varepsilon)$, where $\phi(\varepsilon)=\int_0^1\frac{dy}{y(1-\log y)+\varepsilon}$. Then:
--
--   1. a solution $y_\varepsilon$ exists, and any two solutions coincide on $[0,\phi(\varepsilon)]$;
--   2. $y_\varepsilon'(t)<0$ for every $t\in[0,\phi(\varepsilon))$ (at $t=0$, the right derivative);
--   3. $y_\varepsilon$ is strictly decreasing on $[0,\phi(\varepsilon)]$ and maps $[0,\phi(\varepsilon)]$ bijectively onto $[0,1]$;
--   4. $y_\varepsilon(\phi(\varepsilon))=0$.
--
--   The solution is the continuous counterpart of the recursion (9), and $\phi(\varepsilon)$ is exactly its time to reach $0$.
--
--   Differences from the source:
--   - encoding: a solution of (15)–(16) on (0, ϕ(ε)) with continuous extension at ϕ(ε) → IsSol: continuous on [0, ϕ(ε)], y(0) = 1, y(t) > 0 and y′(t) = y(t)(log y(t) − 1) − ε on (0, ϕ(ε)); reason: the real logarithm in (15) requires y(t) > 0, which Lean's log |y| would not enforce
--   - encoding: a unique solution yε → existence, and any two solutions agree on [0, ϕ(ε)]; reason: a solution is only defined on [0, ϕ(ε)]; values elsewhere are unconstrained
--   - encoding: y′ε(t) < 0 for t ∈ [0, ϕ(ε)) → at t = 0 a right derivative exists and is negative; on (0, ϕ(ε)) the derivative is negative; reason: y is not defined left of 0, so y′(0) is the one-sided derivative
--   - encoding: yε is decreasing and invertible in [0, ϕ(ε)] → StrictAntiOn on [0, ϕ(ε)] and a bijection of [0, ϕ(ε)] onto [0, 1]; reason: "decreasing" in the source is strict (y′ < 0), and [0, 1] is the image (y(0) = 1, y(ϕ(ε)) = 0)
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Proposition 5, p.22

import Mathlib
import Definitions.Def_CompetitionComplexity_Phi
import Definitions.Def_CompetitionComplexity_ODE

namespace CompetitionComplexity

/-- **Proposition 5** (the differential equation).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Proposition 5, p.22:
"For every ε > 0, there exists a unique solution of the differential equation (15)-(16), that we
denote yε. Furthermore, for every t ∈ [0,ϕ(ε)) we have y′ε(t) < 0. In particular, yε is decreasing
and invertible in [0,ϕ(ε)], and yε(ϕ(ε)) = 0."

**Formalization Note.** A solution is only determined on `[0, ϕ(ε)]`, so uniqueness says that two
solutions agree there. `y′(0)` is the right derivative (`y` is not defined left of `0`): it exists
and is negative; on `(0, ϕ(ε))` the derivative is negative. "Decreasing" is strictly decreasing and
"invertible" is a bijection of `[0, ϕ(ε)]` onto its image `[0, 1]`. -/
theorem proposition_5 (ε : ℝ) (hε : 0 < ε) :
    (∃ y : ℝ → ℝ, IsSol ε y) ∧
    (∀ y z : ℝ → ℝ, IsSol ε y → IsSol ε z → Set.EqOn y z (Set.Icc 0 (phi ε))) ∧
    (∀ y : ℝ → ℝ, IsSol ε y →
      (∃ d : ℝ, d < 0 ∧ HasDerivWithinAt y d (Set.Ici 0) 0) ∧
      (∀ t ∈ Set.Ioo 0 (phi ε), deriv y t < 0) ∧
      StrictAntiOn y (Set.Icc 0 (phi ε)) ∧
      Set.BijOn y (Set.Icc 0 (phi ε)) (Set.Icc 0 1) ∧
      y (phi ε) = 0) := by sorry

end CompetitionComplexity
