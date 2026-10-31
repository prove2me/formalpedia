-- Prove2me | Theorems.Thm_BlockchainMarketPower_effort_b
-- name    : BlockchainMarketPower.effort_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:58.480491+00:00
-- url     : https://prove2.me/theorems/2fdc83fe-913f-47f0-afa3-e82a243c3c93
-- title:
--   Proposition 3.1 part 2, adopted: $e^\star_{\mathcal B}$ and $\theta^\star_{\mathcal B}$
-- statement:
--   With blockchain, let $n=|\Xi|\ge1$ and $\Psi\ge0$. The unique symmetric supplier effort is
--
--   $$
--   e^\star_{\mathrm B}=\min\{\Psi^2,1\},
--   $$
--
--   and a supplier accepts at this effort if and only if $\Psi>0$.
--
--   With traceability a supplier's recall risk no longer depends on the other suppliers, so the coordination problem of the no-blockchain regime disappears.
--
--   Differences from the source:
--   - encoding: (1) with the factor Q → profit per unit, for every Ξ ≠ ∅; reason: the proof drops Q on p.32; nothing changes when Q > 0, and (1) is identically 0 when Q = 0
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, Proposition 3.1 part 2, p.18; proof pp.36–37

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- Proposition 3.1 part 2 (adopted), Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.18 (proof
pp.36–37): with blockchain the unique symmetric effort is `e⋆_B = min{Ψ², 1}`, and it is accepted
(`θ⋆_B = 1`) if and only if `Ψ > 0`. -/
theorem effort_b (n : ℕ) (hn : 1 ≤ n) (Ψ : ℝ) (hΨ : 0 ≤ Ψ) :
    (∀ e : ℝ, IsSymEffort .B n Ψ e ↔ e = min (Ψ ^ 2) 1) ∧
      (Accepts .B n Ψ (min (Ψ ^ 2) 1) ↔ 0 < Ψ) := by sorry

end BlockchainMarketPower
