-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_cBar_le_cTilde
-- name    : BOGOPromo.NoStockpile.cBar_le_cTilde
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:52.439647+00:00
-- url     : https://prove2.me/theorems/f436af7f-36a3-49f2-953e-9fb386c29122
-- title:
--   p. 23 (PDF 23) — the BOGO region for the manufacturer includes the PR region: c̄(θ) ≤ c̃(θ)
-- statement:
--   For every $0<\theta\le 1$,
--   $$\bar c(\theta)=\frac{\theta(4\theta-1)}{1+2\theta}-2(1-\theta)\sqrt{\frac{\theta}{1+\theta}}\ \le\ \tilde c(\theta)=\theta-(1-\theta)\sqrt{\frac{2\theta}{1+2\theta}}.$$
--
--   So every cost $c<\bar c(\theta)$ at which the supply chain runs a price reduction (Proposition 4 a)) is also a cost at which it runs a BOGO (Proposition 2 a)); this is how Corollary 4 can compare the two equilibria on the same region.
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, p. 23 (PDF 23), comparison of Figures 3b and 3d

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem cBar_le_cTilde (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : cBar θ ≤ cTilde θ := by sorry

end BOGOPromo.NoStockpile
