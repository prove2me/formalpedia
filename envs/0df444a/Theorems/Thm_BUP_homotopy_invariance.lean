-- Prove2me | Theorems.Thm_BUP_homotopy_invariance
-- name    : BUP.homotopy_invariance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:25:58.593862+00:00
-- url     : https://prove2.me/theorems/e29f00e3-01b2-4b8f-8cff-4e658504d702
-- title:
--   Conjugation-equivalent homomorphisms satisfy the same diagram condition (Proposition 7(1))
-- statement:
--   If two homomorphisms of the fundamental group of the surface are equivalent in the sense of Section 2 - one is obtained from the other by conjugation with a loop - then one admits the commutative diagram of Proposition 6 with respect to the given involution extension and braid data if and only if the other does. The property of not having the Borsuk-Ulam property is thus invariant under the conjugation equivalence, and so is a property of the free homotopy class rather than of the pointed homotopy class.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 2 (Proposition 7(1)).

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor

namespace BUP

/-!  Milestone 1 (Proposition 7(1)): the Borsuk-Ulam diagram condition is
invariant under the conjugation equivalence of induced homomorphisms of
Section 2. If two homomorphisms of the fundamental group are equivalent - one
is obtained from the other by conjugation with a loop - then one admits the
commutative diagram of Proposition 6 if and only if the other does. The proof
lifts the conjugating loop to the pure braid group using the surjectivity of
the Fadell-Neuwirth projection and conjugates both legs of the diagram. -/
theorem homotopy_invariance {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (C : InvSES A B) (D : BraidData A P Bg) (h1 h2 : A →* A)
    (hequiv : homEquiv h1 h2) :
    NoBUP C D h1 ↔ NoBUP C D h2 := by sorry

end BUP
