-- Prove2me | Theorems.Thm_BlockchainMarketPower_accepts_nb
-- name    : BlockchainMarketPower.accepts_nb
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:38.697249+00:00
-- url     : https://prove2.me/theorems/a3ff6cb5-a7db-4aac-babd-fda6d1662ea1
-- title:
--   Proposition 3.1 part 2, not adopted: $e^\star_{\mathcal{NB}}$ and $\theta^\star_{\mathcal{NB}}$
-- statement:
--   Without blockchain, let $n=|\Xi|\ge1$ and $\Psi\ge0$. The effort
--
--   $$
--   e^\star_{\mathrm{NB}}=\begin{cases}\min\{\Psi^2,1\}&\text{if }n=1,\\ 0&\text{if }n>1\end{cases}
--   $$
--
--   is a symmetric effort, and a supplier accepts at this effort if and only if $n=1$ and $\Psi>0$. Moreover, a symmetric effort $e$ of any kind is accepted if and only if $e>0$.
--
--   This is the printed supplier behaviour without blockchain, together with the acceptance rule at the other solutions of the table.
--
--   Differences from the source:
--   - generalization: θ⋆_NB is given at the printed effort → acceptance is also decided at every symmetric effort: accepted if and only if e > 0; reason: the printed θ⋆_NB is the case e = e⋆_NB
--   - reading: §3.1: accept and effort are simultaneous and (2) depends on the accepting set Γ → symmetric fixed point with exponent |Ξ| - 1, assuming all of Ξ produce, then acceptance tested at that effort; reason: this is what the proof computes on pp.32, 36; the paper names no other solution of the supplier stage
--   - encoding: (1) with the factor Q → profit per unit, for every Ξ ≠ ∅; reason: the proof drops Q on p.32; nothing changes when Q > 0, and (1) is identically 0 when Q = 0
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, Proposition 3.1 part 2, p.18; proof pp.32–33

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- Proposition 3.1 part 2 (not adopted), Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.18, and
p.33: the printed effort `e⋆_NB` is a symmetric effort, and it is accepted (`θ⋆_NB = 1`) if and only if
`|Ξ| = 1` and `Ψ > 0`. Moreover every symmetric effort is accepted exactly when it is positive. -/
theorem accepts_nb (n : ℕ) (hn : 1 ≤ n) (Ψ : ℝ) (hΨ : 0 ≤ Ψ) :
    IsSymEffort .NB n Ψ (printedEffort .NB n Ψ) ∧
      (Accepts .NB n Ψ (printedEffort .NB n Ψ) ↔ n = 1 ∧ 0 < Ψ) ∧
      ∀ e : ℝ, IsSymEffort .NB n Ψ e → (Accepts .NB n Ψ e ↔ 0 < e) := by sorry

end BlockchainMarketPower
