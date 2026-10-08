-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_eq_44
-- name    : CachonCoord.InternalMarket.eq_44
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:56:20.115696+00:00
-- url     : https://prove2.me/theorems/73bfe571-848a-4069-8f0e-d39183a5b937
-- title:
--   Eq. (44), p. 93 — revenue is strictly concave in γ and γ°(α) = α₁^η/(α₁^η + α₂^η) is the unique optimal share
-- statement:
--   Let $\eta>1$, $\alpha_1,\alpha_2>0$ and $Q>0$, and let
--   $$
--   \pi(\gamma,\alpha,Q)=\big(\alpha_1\gamma^{(\eta-1)/\eta}+\alpha_2(1-\gamma)^{(\eta-1)/\eta}\big)Q^{(\eta-1)/\eta}
--   $$
--   be the retailers' total revenue when retailer one receives the share $\gamma$ of the output $Q$. Then $\gamma\mapsto\pi(\gamma,\alpha,Q)$ is strictly concave on $[0,1]$, and
--   $$
--   \gamma^o(\alpha)=\frac{\alpha_1^\eta}{\alpha_1^\eta+\alpha_2^\eta}\in[0,1]
--   $$
--   is its unique maximizer over $[0,1]$. In particular the optimal share does not depend on the output $Q$.
--
--   This is the supply chain's optimal allocation of output between the retailers, the benchmark the internal market has to reproduce.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, Eq. (44), p. 93

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- Eq. (44), §6.9.1, p. 93 (Cachon 2003, 3rd draft): for demand realizations `α₁, α₂ > 0`,
elasticity `η > 1` and output `Q > 0`, total retailer revenue `γ ↦ π(γ, α, Q)` is strictly
concave on `[0, 1]`, and the share `γ°(α) = α₁^η / (α₁^η + α₂^η)` lies in `[0, 1]` and is its unique
maximizer there. -/
theorem eq_44 (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hQ : 0 < Q) :
    StrictConcaveOn ℝ (Set.Icc 0 1) (fun γ => revenue η α₁ α₂ γ Q) ∧
    optShare η α₁ α₂ ∈ Set.Icc (0 : ℝ) 1 ∧
    IsMaxOn (fun γ => revenue η α₁ α₂ γ Q) (Set.Icc 0 1) (optShare η α₁ α₂) ∧
    ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      IsMaxOn (fun γ' => revenue η α₁ α₂ γ' Q) (Set.Icc 0 1) γ → γ = optShare η α₁ α₂ := by sorry

end CachonCoord.InternalMarket
