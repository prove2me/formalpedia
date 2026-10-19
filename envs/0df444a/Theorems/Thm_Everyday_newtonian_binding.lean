-- Prove2me | Theorems.Thm_Everyday_newtonian_binding
-- name    : Everyday.newtonian_binding
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T00:15:03.667162+00:00
-- url     : https://prove2.me/theorems/ce5f139d-dfc8-4783-89a1-331c969447c1
-- title:
--   Gravity at the everyday level: the Newtonian binding energy of positive masses at distinct positions is negative
-- statement:
--   The image's gravity label is the Einstein–Hilbert term (m_p²/2) R, and the post notes that gravity is understood "perfectly well at the everyday level": there, the Einstein–Hilbert term reduces to Newtonian gravitation. The item is the Newtonian sector's everyday content: gravitation binds. For finitely many positive masses at pairwise distinct positions, the gravitational binding energy — half the sum of the pair energies -G m_i m_j / |q_i - q_j| over ordered pairs of distinct particles — is strictly negative. Assemblies of positive masses attract, and the binding energy of an everyday gravitational system is negative.
--
--   **Formalization Note** The sum runs over ordered pairs of distinct particles, so each unordered pair is counted twice; the factor 2 in the denominator implements the halving, making the sum the binding energy. The hypotheses are positivity of G, positivity of every mass, distinctness of distinct particles' positions, and the existence of at least two particles, carried as the nontriviality of the index type. The index type also carries decidable equality, the proof-irrelevant bookkeeping instance required to form the filtered sum; it imposes no restriction on the physical content. The conclusion is the strict negativity of the binding sum.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the gravity term (m_p²/2) R and the post's remark on the everyday level

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open scoped BigOperators

namespace Everyday

/-- Gravity, at the everyday level: Newtonian gravitation is
attractive. For finitely many positive masses at pairwise distinct
positions, the gravitational binding energy — half the sum of the pair
energies over ordered pairs of distinct particles — is strictly
negative. This is the everyday face of the (m_p²/2) R sector: at the
everyday level the Einstein–Hilbert term reduces to Newtonian
gravitation, and Newtonian gravitation binds. -/
theorem newtonian_binding (ι : Type) [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (G : ℝ) (m : ι → ℝ) (q : ι → ℝ)
    (hG : 0 < G) (hm : ∀ i, 0 < m i) (hq : ∀ i j, i ≠ j → q i ≠ q j) :
    ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 ≠ p.2),
      -(G * m p.1 * m p.2 / (2 * |q p.1 - q p.2|)) < 0 := by sorry

end Everyday
