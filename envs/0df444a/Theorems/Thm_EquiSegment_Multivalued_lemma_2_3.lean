-- Prove2me | Theorems.Thm_EquiSegment_Multivalued_lemma_2_3
-- name    : EquiSegment.Multivalued.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:31.352274+00:00
-- url     : https://prove2.me/theorems/d0670a92-d465-4bc0-a121-72dba89647f3
-- title:
--   Lemma 2.3 — prime-step refinement of a nice multivalued function
-- statement:
--   Let $p$ be prime. Let $\varphi$ continuously represent a nice multivalued function on the cylinder and satisfy $\varphi([a,a],y)=y$ for all degenerate segments and cylinder values. Then there is another such representation $\psi$, also satisfying $\psi([a,a],y)=y$, with this property: whenever $I=[a,b]\in\mathcal I$ and $y\in(-1,1)$ satisfy $\psi(I,y)=0$, the segment $I$ has a partition into exactly $p$ consecutive possibly degenerate segments $I_1,\ldots,I_p$ for which
--
--   $$
--   \varphi(I_1,y)=\cdots=\varphi(I_p,y)=0.
--   $$
--
--   This is the prime-step refinement used in the proof of Theorem 1.1.
--
--   **Formalization Note** The representation hypothesis means continuity on the cylinder with negative values at its bottom and positive values at its top. Along with the degenerate identity, this is equivalent to the paper's “corresponds to a nice multivalued function” convention via Lemma 2.2.
-- source:
--   Avvakumov & Karasev, Equipartition of a Segment, arXiv:2009.09862v4, p. 3, Lemma 2.3, equation (2.1)

import Definitions.Def_EquiSegment_Multivalued_Setting

namespace EquiSegment.Multivalued

/-- Avvakumov–Karasev, Lemma 2.3, p. 3. -/
theorem lemma_2_3 (φ : ℝ × ℝ → ℝ → ℝ) (p : ℕ)
    (hp : p.Prime) (hφ : IsRep φ) (hdeg : DegId φ) :
    ∃ ψ : ℝ × ℝ → ℝ → ℝ, IsRep ψ ∧ IsNice (zeroSet ψ) ∧ DegId ψ ∧
      ∀ s ∈ Seg, ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        ψ s y = 0 → IsZeroPartition φ p s y := by sorry

end EquiSegment.Multivalued
