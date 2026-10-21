-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_4_6_pricing_stage
-- name    : BrandLicensing.Intensive.eq_4_6_pricing_stage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:00.727297+00:00
-- url     : https://prove2.me/theorems/87e5392b-9581-405f-81c1-37cc2a2038f3
-- title:
--   Eqs. (4)–(6), p. 3187 — the monopoly price of the extension and the resulting output and profit
-- statement:
--   Consider the extension market of the brand-extension model with efforts $e_C,e_E$ and royalty $s$ (any real numbers), and write $a=e_E+(1-\alpha)e_C$ for the perceived quality index. A seller charging price $p$ sells $\max\{\rho(a-p),0\}$ units and earns $(p-s)\max\{\rho(a-p),0\}$. Then:
--
--   1. for every price $p$, this profit is at most $\pi^M=\rho\max\{a-s,0\}^2/4$;
--   2. the monopoly price $p^M=(a+s)/2$ attains $\pi^M$;
--   3. if $s\le a$, the output at $p^M$ is
--   $$q^M=\rho\,\frac{e_E+(1-\alpha)e_C-s}{2}.$$
--
--   This is the pricing stage of the game, which the paper solves first; it justifies using the reduced profit $\pi^M$ of (6) in every later stage, both for the licensee and (with $s=0$) for the brand owner under in-house development.
--
--   **Formalization Note** Only $\rho\ge0$ from the standing assumptions is used. The positive part handles the case $s>a$, where nothing is sold and $\pi^M=0$.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3187 (PDF 7), §4.1, eqs. (4), (5), (6)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- §4.1, (4)–(6), p. 3187: the monopoly price (4) maximizes the extension seller's profit, the
maximum is (6), and when the margin is non-negative the output at (4) is (5). -/
theorem eq_4_6_pricing_stage (P : Params) (hP : P.Standing) (eC eE s : ℝ) :
    (∀ p, extProfitAt P eC eE s p ≤ piM P eC eE s) ∧
    extProfitAt P eC eE s (pM P eC eE s) = piM P eC eE s ∧
    (s ≤ eE + (1 - P.α) * eC →
      demand P eC eE (pM P eC eE s) = P.ρ * (eE + (1 - P.α) * eC - s) / 2) := by sorry
end BrandLicensing.Intensive
