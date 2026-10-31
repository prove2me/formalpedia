-- Prove2me | Theorems.Thm_BlockchainMarketPower_welfare_chain
-- name    : BlockchainMarketPower.welfare_chain
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:31.898316+00:00
-- url     : https://prove2.me/theorems/45cf9405-382a-49b9-8d16-6143220481b6
-- title:
--   Proof of Proposition 4.1: the chain (a)–(c)
-- statement:
--   Let $\Psi^\star_{\mathrm{NB}}$ be the root of $\Lambda(\cdot,P^\star_{\mathrm{NB}},1)$ in $(0,P^\star_{\mathrm{NB}})$ and $\Psi^\star_{\mathrm B}$ the root of $\Lambda(\cdot,P^\star_{\mathrm B},N)$ in $(0,P^\star_{\mathrm B})$. Then
--
--   $$
--   f\bigl(P^\star_{\mathrm{NB}},\Psi^\star_{\mathrm{NB}};\gamma\bigr)
--   <f\bigl(P^\star_{\mathrm{B}},\Psi^\star_{\mathrm{NB}};\gamma\bigr)
--   \le f\bigl(P^\star_{\mathrm{B}},\Psi^\star_{\mathrm{NB}};\tfrac\gamma N\bigr)
--   \le f\bigl(P^\star_{\mathrm{B}},\Psi^\star_{\mathrm{B}};\tfrac\gamma N\bigr).
--   $$
--
--   The three steps are the price effect, the risk effect at fixed prices, and the reoptimization of the supplier price. Together they give $\Omega^\star>0$.
--
--   Differences from the source:
--   - encoding: Ψ⋆ as the argmax; the last equality with γ/|Ξ⋆_B| → Ψ⋆ as the root of Λ in (0, P⋆); that equality is not stated; reason: psi_star identifies the two descriptions, and |Ξ⋆_B| = N is in proposition_3_1_manufacturer
--   - encoding: N ∈ ℕ; α ∈ [α̲, ᾱ] with 1/2 < α̲ < ᾱ < 1; suppliers {1, ..., N} → 0 < N; 1/2 < α < 1; suppliers Fin N; reason: the same instances
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 4.1, p.40

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- The chain (a)–(c), Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 4.1, p.40:
`f(P⋆_NB, Ψ⋆_NB; γ) < f(P⋆_B, Ψ⋆_NB; γ) ≤ f(P⋆_B, Ψ⋆_NB; γ/N) ≤ f(P⋆_B, Ψ⋆_B; γ/N)`. -/
theorem welfare_chain {N : ℕ} (p : Params N) (ΨNB ΨB : ℝ)
    (hNB : IsInteriorRoot p.γ 1 (p.priceStar .NB) ΨNB)
    (hB : IsInteriorRoot p.γ N (p.priceStar .B) ΨB) :
    f (p.priceStar .NB) ΨNB p.γ < f (p.priceStar .B) ΨNB p.γ ∧
      f (p.priceStar .B) ΨNB p.γ ≤ f (p.priceStar .B) ΨNB (p.γ / (N : ℝ)) ∧
      f (p.priceStar .B) ΨNB (p.γ / (N : ℝ)) ≤ f (p.priceStar .B) ΨB (p.γ / (N : ℝ)) := by sorry

end BlockchainMarketPower
