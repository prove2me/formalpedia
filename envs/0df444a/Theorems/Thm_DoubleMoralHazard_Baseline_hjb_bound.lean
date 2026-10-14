-- Prove2me | Theorems.Thm_DoubleMoralHazard_Baseline_hjb_bound
-- name    : DoubleMoralHazard.Baseline.hjb_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:42.546724+00:00
-- url     : https://prove2.me/theorems/3f1b22c5-f746-4c88-9803-e286723030c5
-- title:
--   (B.12)–(B.16), App. B.6, p. 51 — with F = Fᵢ, the drift Φ of (B.7) is ≤ 0 at every (Hᵘ, Hᵒ) with Hᵘ ≥ Rᵘ, pHᵘ + (1−p)Hᵒ ≥ β
-- statement:
--   Fix a scenario $i\in\{1,2,3\}$ ($c\le\mu pR^u$; $\mu pR^u<c<\mu R^u$; $c\ge\mu R^u$) and let $F$ be a solution of the scenario's value-function equation in the sense of the file `HJB`, which is moreover concave and differentiable on $[0,\infty)$ with $F'(w)\ge-1$ for $w\ge0$ (the properties Lemma 4 provides). Then for every promised utility $w\ge0$ and every pair of jump sizes $(H^u,H^o)$ with
--   $$H^u\ge R^u\quad\text{(IC-truthful)},\qquad pH^u+(1-p)H^o\ge\beta\quad\text{(IC-effort)},\qquad w+H^o\ge0,$$
--   the drift of (B.7) is nonpositive:
--   $$\Phi=\mu pR^u+\mu(1-p)R^o+F'(w)[rw-\mu pH^u-\mu(1-p)H^o]-rF(w)+(F(w+H^u)-F(w))\mu p+(F(w+H^o)-F(w))\mu(1-p)-c\ \le\ 0.$$
--
--   This is the pointwise inequality that the verification lemma (Lemma 14) needs in order to bound the principal's utility under any incentive compatible contract by $F_i$; the paper derives it from the optimizers (B.13)–(B.15) of the static problem (B.12) and the equations (2.9), (2.11), (2.13).
--
--   **Formalization Note** The condition $w+H^o\ge0$ is added: (B.12) constrains $H^u,H^o$ only by (IC-truthful) and (IC-effort), so $H^o$ may be negative, and $F(w+H^o)$ with $w+H^o<0$ lies outside the domain $[0,\infty)$ of $F$. A jump that can occur keeps the promised utility nonnegative (individual rationality), so the added condition loses nothing in the application. Scenario 2 uses the corrected (2.11). The derivative is relative to $[0,\infty)$.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), p. 51, Appendix B.6, (B.12)–(B.16) and the two unnumbered displays after (B.16), with (B.7), p. 49

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB

namespace DoubleMoralHazard.Baseline

open Set

/-- Appendix B.6, (B.12)–(B.16), p. 51: in each scenario, for the value function `Fᵢ` (a solution
of the scenario's equation, concave and differentiable on `[0, ∞)` with `F' ≥ -1`), the drift `Φ`
of (B.7) is nonpositive at every promised utility `w ≥ 0` and every pair of jumps `(Hᵘ, Hᵒ)`
satisfying (IC-truthful) `Hᵘ ≥ Rᵘ` and (IC-effort) `p Hᵘ + (1 - p) Hᵒ ≥ β`, provided the jump
`Hᵒ` keeps the promised utility nonnegative, `w + Hᵒ ≥ 0`. -/
theorem hjb_bound (P : Params) :
    (P.c ≤ P.mu * P.p * P.Ru → ∀ F : ℝ → ℝ, IsSol1 P F → ConcaveOn ℝ (Ici 0) F →
      DifferentiableOn ℝ F (Ici 0) → (∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w) →
      ∀ w Hu Ho : ℝ, 0 ≤ w → P.Ru ≤ Hu → P.beta ≤ P.p * Hu + (1 - P.p) * Ho → 0 ≤ w + Ho →
        Phi P F w Hu Ho ≤ 0) ∧
    (P.mu * P.p * P.Ru < P.c ∧ P.c < P.mu * P.Ru → ∀ F : ℝ → ℝ, IsSol2 P F →
      ConcaveOn ℝ (Ici 0) F →
      DifferentiableOn ℝ F (Ici 0) → (∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w) →
      ∀ w Hu Ho : ℝ, 0 ≤ w → P.Ru ≤ Hu → P.beta ≤ P.p * Hu + (1 - P.p) * Ho → 0 ≤ w + Ho →
        Phi P F w Hu Ho ≤ 0) ∧
    (P.mu * P.Ru ≤ P.c → ∀ F : ℝ → ℝ, IsSol3 P F → ConcaveOn ℝ (Ici 0) F →
      DifferentiableOn ℝ F (Ici 0) → (∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w) →
      ∀ w Hu Ho : ℝ, 0 ≤ w → P.Ru ≤ Hu → P.beta ≤ P.p * Hu + (1 - P.p) * Ho → 0 ≤ w + Ho →
        Phi P F w Hu Ho ≤ 0) := by sorry

end DoubleMoralHazard.Baseline
