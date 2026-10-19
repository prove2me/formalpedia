-- Prove2me | Theorems.Thm_EquiSegment_Multivalued_claim_4_3
-- name    : EquiSegment.Multivalued.claim_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:21.892892+00:00
-- url     : https://prove2.me/theorems/969c7a98-90e7-4760-a240-ed93ce2681f6
-- title:
--   Claim 4.3 — projected solutions separate a parameter rectangle
-- statement:
--   Let $p$ be prime and $\varphi$ satisfy the representation and degenerate identity conditions. Let $s_0\le s_1$ and let $I(s)$ be a continuous family of segments for $s\in[s_0,s_1]$. In the rectangle $R=[s_0,s_1]\times[-1,1]$, form the projected solution set
--
--   $$
--   T=\{(s,y)\in R: I(s)\text{ has a partition into }p\text{ consecutive segments }I_j
--   \text{ with }\varphi(I_j,y)=0\text{ for all }j\}.
--   $$
--
--   Then $T$ separates $[s_0,s_1]\times\{-1\}$ from $[s_0,s_1]\times\{1\}$ in $R$. Separation has the connected-component sense of Definition 2.1. This is the paper's parameter-family step.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 8, Claim 4.3

import Definitions.Def_EquiSegment_Multivalued_Setting

namespace EquiSegment.Multivalued

/-- Avvakumov–Karasev, Claim 4.3, p. 8. -/
theorem claim_4_3 (φ : ℝ × ℝ → ℝ → ℝ) (p : ℕ)
    (hp : p.Prime) (hφ : IsRep φ) (hdeg : DegId φ)
    (s₀ s₁ : ℝ) (hs : s₀ ≤ s₁) (γ : ℝ → ℝ × ℝ)
    (hγ : ContinuousOn γ (Set.Icc s₀ s₁))
    (hγSeg : Set.MapsTo γ (Set.Icc s₀ s₁) Seg) :
    Separates (Set.Icc s₀ s₁ ×ˢ Set.Icc (-1 : ℝ) 1)
      {q | q ∈ Set.Icc s₀ s₁ ×ˢ Set.Icc (-1 : ℝ) 1 ∧
        (γ q.1, q.2) ∈ projZ φ p}
      (Set.Icc s₀ s₁ ×ˢ {(-1 : ℝ)})
      (Set.Icc s₀ s₁ ×ˢ {(1 : ℝ)}) := by sorry

end EquiSegment.Multivalued
