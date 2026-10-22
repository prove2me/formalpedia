-- Prove2me | Theorems.Thm_BUP_thm3_lifts
-- name    : BUP.thm3_lifts
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:30:13.671758+00:00
-- url     : https://prove2.me/theorems/b837464f-299d-47c3-bb16-672b74d85f82
-- title:
--   The Klein bottle classes with the Borsuk-Ulam property are exactly the classes that lift to the torus (Theorem 3)
-- statement:
--   In the idealized Klein bottle world with its double covering by the torus, the homotopy class with induced homomorphism h does not have the Borsuk-Ulam property if and only if h lifts through the covering: every value of h lies in the image of the covering injection of the torus. A class of the Klein bottle has the Borsuk-Ulam property with respect to the free involution exactly when it lifts to the torus. The proof separates the homomorphisms of the Klein bottle group according to the type analysis of Proposition 35: the non-liftable ones admit the explicit witnesses of Proposition 38, while the liftable ones inherit the Borsuk-Ulam property from the triple of the Klein bottle, the involution, and the torus as in Proposition 39.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 6 (Theorem 3, from Propositions 35, 38, and 39).

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor

namespace BUP

/-!  The goal (Theorem 3, from Propositions 38 and 39): the classification of
the homotopy classes of selfmaps of the Klein bottle that have the
Borsuk-Ulam property with respect to a free involution. In the idealized Klein
bottle world, the homotopy class with induced homomorphism h does not have the
Borsuk-Ulam property if and only if h does not lift through the double
covering of the Klein bottle by the torus: a class has the Borsuk-Ulam
property exactly when every value of its induced homomorphism lies in the
image of the covering injection. The proof separates the homomorphisms of the
Klein bottle group according to the type analysis of Proposition 35: the
non-liftable ones admit the explicit witnesses of Proposition 38, while the
liftable ones inherit the Borsuk-Ulam property from the triple of the Klein
bottle, the involution, and the torus as in Proposition 39. -/
theorem thm3_lifts {A B P Bg T : Type*} [Group A] [Group B] [Group P] [Group Bg] [Group T]
    (W : KleinWorld A B P Bg T) (h : A →* A) :
    NoBUP W.C W.D h ↔ ¬ W.LiftsTor h := by sorry

end BUP
