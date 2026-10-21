-- Prove2me | Theorems.Thm_EquiSegment_Multivalued_eq_4_2
-- name    : EquiSegment.Multivalued.eq_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:34.956744+00:00
-- url     : https://prove2.me/theorems/2dc60f58-90de-4826-aa78-9721c6dec11b
-- title:
--   Equation (4.2) — zeros on degenerate segments
-- statement:
--   Let $p$ be prime and $\varphi$ satisfy the representation and degenerate identity conditions. For $I' = \{[a,a]:a\in[0,1]\}$, the projected zero set $Z_p(\varphi)$ has precisely the zero level on degenerate segments:
--
--   $$
--   Z_p(\varphi)\cap(I'\times\mathbb R)=I'\times\{0\}.
--   $$
--
--   The equality is stated for cylinder values $y\in[-1,1]$, where $Z_p(\varphi)$ is defined. It is the boundary condition used to obtain the identity $\psi([a,a],y)=y$ in Lemma 2.3.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 9, equation (4.2)

import Definitions.Def_EquiSegment_Multivalued_Setting

namespace EquiSegment.Multivalued

/-- Avvakumov–Karasev, equation (4.2), p. 9. -/
theorem eq_4_2 (φ : ℝ × ℝ → ℝ → ℝ) (p : ℕ)
    (hp : p.Prime) (hφ : IsRep φ) (hdeg : DegId φ) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      (((a, a), y) ∈ projZ φ p ↔ y = 0) := by sorry

end EquiSegment.Multivalued
