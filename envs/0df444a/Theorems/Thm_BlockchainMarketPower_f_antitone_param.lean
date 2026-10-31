-- Prove2me | Theorems.Thm_BlockchainMarketPower_f_antitone_param
-- name    : BlockchainMarketPower.f_antitone_param
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:21.008081+00:00
-- url     : https://prove2.me/theorems/865fdb0d-ecb5-4299-b520-2d373fc7112e
-- title:
--   Proof of Proposition 4.1, step (b): $f$ is decreasing in its parameter
-- statement:
--   Let $0\le\Psi\le1$ and let $P$ be real. The map $\gamma'\mapsto f(P,\Psi;\gamma')$ is decreasing: if $\gamma_1\le\gamma_2$ then $f(P,\Psi;\gamma_2)\le f(P,\Psi;\gamma_1)$.
--
--   This compares the two regimes' risk penalties, and it is step (b) of the proof of the main result.
--
--   Differences from the source:
--   - reading: "f(P, Ψ; γ) is decreasing in terms of the parameter γ", no domain for Ψ → 0 ≤ Ψ ≤ 1; reason: for Ψ > 1 the coefficient Ψ(1 - Ψ) is negative and the claim is false; the proof uses it at Ψ⋆_NB ∈ (0, 1)
--   - generalization: over [0, +∞) → over all real parameters; reason: the proof of the antitone claim does not use the sign; [0, +∞) is a special case
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 4.1, step (b), p.40

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- `f` is decreasing in its parameter, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of
Proposition 4.1, step (b), p.40: for `0 ≤ Ψ ≤ 1` the map `γ' ↦ f(P, Ψ; γ')` is antitone. -/
theorem f_antitone_param (P Ψ : ℝ) (hΨ₀ : 0 ≤ Ψ) (hΨ₁ : Ψ ≤ 1) :
    Antitone (fun γ' => f P Ψ γ') := by sorry

end BlockchainMarketPower
