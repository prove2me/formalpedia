-- Prove2me | Theorems.Thm_ConnesFeldmanWeiss_isAmenableRel_orbit_quotient_of_isAmenableGroup
-- name    : ConnesFeldmanWeiss.isAmenableRel_orbit_quotient_of_isAmenableGroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T16:18:17.306266+00:00
-- url     : https://prove2.me/theorems/22c7ac64-1c7c-4225-a12b-1de45f10ee6e
-- title:
--   Proof of Corollary 14 (external, Zimmer) — a discrete subgroup acts amenably on G/P for P closed and amenable
-- statement:
--   Let $G$ be a second countable, locally compact Hausdorff group, $P$ a closed subgroup that is amenable as a locally compact group (`IsAmenableGroup`: a left invariant mean on $L^\infty(P)$ for Haar measure), and $\Gamma$ a discrete subgroup. Give $G/P$ its Borel structure and a finite measure $\nu$ whose null sets are exactly the sets with Haar-null preimage in $G$ (the canonical measure class of $G/P$). Then the orbit relation of $\Gamma$ on $G/P$, the pairs $(x, \gamma x)$ with $\gamma \in \Gamma$, is amenable for $\nu$ (`Monod.IsAmenableRel`).
--
--   Second countability makes $G/P$ standard Borel and $\Gamma$ countable, the setting of §1. The local compactness of $P$, assumed as an instance, follows from its being closed.
-- source:
--   Zimmer, R. J., Cocycles and the structure of ergodic group actions, Israel J. Math. 26 (1977) 214–220, https://doi.org/10.1007/BF03007643, p. 446, proof of Corollary 14

import Mathlib
import Definitions.Def_ConnesFeldmanWeiss
import Definitions.Def_Monod_PiecewiseProjective

namespace ConnesFeldmanWeiss

theorem isAmenableRel_orbit_quotient_of_isAmenableGroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (P : Subgroup G) (hP : IsClosed (P : Set G))
    [LocallyCompactSpace P] (hPamen : IsAmenableGroup P) (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    (ν : MeasureTheory.Measure (G ⧸ P)) [MeasureTheory.IsFiniteMeasure ν]
    (hν : ∀ A : Set (G ⧸ P), MeasurableSet A →
      (ν A = 0 ↔ MeasureTheory.Measure.haar ((QuotientGroup.mk : G → G ⧸ P) ⁻¹' A) = 0)) :
    Monod.IsAmenableRel ν {p : (G ⧸ P) × (G ⧸ P) | ∃ γ ∈ Γ, γ • p.1 = p.2} := by
  sorry

end ConnesFeldmanWeiss
