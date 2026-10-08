-- Prove2me | Theorems.Thm_ApproachRegret_Calibration_claim1_l1_dist
-- name    : ApproachRegret.Calibration.claim1_l1_dist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:28:41.275979+00:00
-- url     : https://prove2.me/theorems/79cb327a-b0d7-49a4-8a91-9393ebd6bd98
-- title:
--   Claim 1 (proof) — the ℓ₁ distance to $B_1(\varepsilon/2)$ is $\max\{0,\|x\|_1-\varepsilon/2\}$
-- statement:
--   Let $x\in\mathbb R^n$ and $\varepsilon>0$, and let $B_1(\varepsilon/2)=\{y:\|y\|_1\le\varepsilon/2\}$. Then the ℓ₁ distance from $x$ to this ball is attained and equals
--   $$\mathrm{dist}_1\bigl(x,B_1(\varepsilon/2)\bigr)=\min_{y:\|y\|_1\le\varepsilon/2}\|x-y\|_1=\max\Bigl\{0,\ -\frac\varepsilon2+\|x\|_1\Bigr\}.$$
--
--   Applied to the calibration vector $c_T$, this identity is Claim 1: when $c_T\notin B_1(\varepsilon/2)$, the $(\ell_1,\varepsilon)$-calibration rate $C^\varepsilon_T$ is the ℓ₁ distance of $c_T$ to $B_1(\varepsilon/2)$. It turns calibration into a question of approaching the ball $B_1(\varepsilon/2)$.
--
--   **Formalization Note** The literal Claim 1 is about the calibration vector of the sampled forecasts; it is stated here through the identity its proof rests on, which is the general fact. The minimum is stated with `IsLeast` on the image of the ball, so it is attained.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Claim 1 and its proof, p. 40

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game

namespace ApproachRegret.Calibration

/-- Claim 1 (p. 40), the identity of its proof: for every `x ∈ ℝⁿ` and `ε > 0`,
`dist₁(x, B₁(ε/2)) = min_{‖y‖₁ ≤ ε/2} ‖x − y‖₁ = max {0, −ε/2 + ‖x‖₁}`, the minimum attained. -/
theorem claim1_l1_dist {n : ℕ} (x : ApproachRegret.ToOLO.E n) (ε : ℝ) (hε : 0 < ε) :
    IsLeast ((fun y => l1norm (x - y)) '' l1Ball n (ε / 2)) (max 0 (-(ε / 2) + l1norm x)) := by sorry

end ApproachRegret.Calibration
