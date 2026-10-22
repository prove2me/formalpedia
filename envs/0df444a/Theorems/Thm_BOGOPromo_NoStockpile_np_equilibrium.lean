-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_np_equilibrium
-- name    : BOGOPromo.NoStockpile.np_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:35.168108+00:00
-- url     : https://prove2.me/theorems/ddde5882-b2c6-4dbe-80b5-d37e06e6ff95
-- title:
--   Table 3 (2nd column), p. 16 (PDF 16) — the no-promotion equilibrium
-- statement:
--   Let the unit production cost satisfy $0\le c<1$ and consider the game in which the retailer can only set a single price. An equilibrium (manufacturer leading, retailer best-responding at every wholesale price in $(0,1]$) exists, and in every equilibrium
--   $$w=\frac{1+c}{2},\quad p=\frac{3+c}{4},\quad D=\frac{1-c}{2},\quad \pi_r=\frac{(1-c)^2}{8},\quad \pi_m=\frac{(1-c)^2}{4}.$$
--
--   This is the benchmark against which Corollary 4 compares the BOGO and PR outcomes.
--
--   **Formalization Note** The page allows $0\le c\le 1$; the case $c=1$ is excluded. There the manufacturer's profit $(w-1)(1-w)$ forces $w=1$, but at $w=1$ every retail price $p\ge 1$ is a best response (profit $0$), so the retail price $(3+c)/4=1$ of the table is one equilibrium outcome, not the only one.
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, p. 16 (PDF 16), Table 3 (2nd column, No Promotion)

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem np_equilibrium (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∃ (w : ℝ) (r : ℝ → ℝ), IsEqN c w r) ∧
    ∀ (w : ℝ) (r : ℝ → ℝ), IsEqN c w r →
      w = (1 + c) / 2 ∧ r w = (3 + c) / 4 ∧ npDemand (r w) = (1 - c) / 2 ∧
      npProfit w (r w) = (1 - c) ^ 2 / 8 ∧ (w - c) * npDemand (r w) = (1 - c) ^ 2 / 4 := by sorry

end BOGOPromo.NoStockpile
