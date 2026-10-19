-- Prove2me | Theorems.Thm_EquiSegment_Multivalued_claim_4_4
-- name    : EquiSegment.Multivalued.claim_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:34.735697+00:00
-- url     : https://prove2.me/theorems/4c24a165-9b7e-48df-8dc0-6812cbbb9f69
-- title:
--   Claim 4.4 — projected solutions separate the cylinder
-- statement:
--   Let $p$ be prime and $\varphi$ satisfy the representation and degenerate identity conditions. Write $Z_p(\varphi)$ for all pairs $(I,y)$ in the cylinder such that $I$ admits a partition into $p$ consecutive possibly degenerate segments $I_j$ with $\varphi(I_j,y)=0$ for every $j$. Then
--
--   $$
--   Z_p(\varphi)\text{ separates }\mathcal I\times\{-1\}\text{ from }\mathcal I\times\{1\}
--   \text{ in }\mathcal I\times[-1,1].
--   $$
--
--   This gives the projected zero set the key separation property required of a nice multivalued function.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 9, Claim 4.4

import Definitions.Def_EquiSegment_Multivalued_Setting

namespace EquiSegment.Multivalued

/-- Avvakumov–Karasev, Claim 4.4, p. 9. -/
theorem claim_4_4 (φ : ℝ × ℝ → ℝ → ℝ) (p : ℕ)
    (hp : p.Prime) (hφ : IsRep φ) (hdeg : DegId φ) :
    Separates Cyl (projZ φ p) Bottom Top := by sorry

end EquiSegment.Multivalued
