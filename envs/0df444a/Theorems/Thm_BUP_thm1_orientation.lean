-- Prove2me | Theorems.Thm_BUP_thm1_orientation
-- name    : BUP.thm1_orientation
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:29:19.54663+00:00
-- url     : https://prove2.me/theorems/ae8d4db8-20de-4133-bb1f-f8b3a58dd032
-- title:
--   No homotopy class of the torus has the Borsuk-Ulam property for an orientation-preserving free involution (Theorem 1)
-- statement:
--   In the idealized torus world whose deck transformation preserves orientation - acting trivially on the fundamental group - every homomorphism h of the fundamental group admits the commutative diagram of Proposition 6: no homotopy class of selfmaps of the torus has the Borsuk-Ulam property with respect to the orientation-preserving free involution. The witnesses of the criterion of Lemma 26 are constructed explicitly from the integral matrix of h, rounding the first column parities as in Proposition 27. Together with the transport along equivalences of involutions this covers every free involution of the torus equivalent to an orientation-preserving one.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 5 (Proposition 27 and Theorem 1, with Propositions 9 and 25).

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor

namespace BUP

/-!  Milestone 6 (Proposition 27, and Theorem 1 with Propositions 9 and 25):
with respect to an orientation-preserving free involution of the torus, no
homotopy class of selfmaps has the Borsuk-Ulam property. In the idealized
torus world whose deck transformation acts trivially on the fundamental group,
every induced homomorphism h admits the commutative diagram of Proposition 6.
The proof constructs the witnesses of Lemma 26 explicitly from the integral
matrix of h, rounding the first column parities as in Proposition 27; together
with the transport of milestone 2 this covers every free involution
equivalent to the orientation-preserving one. -/
theorem thm1_orientation {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (hp : TorusPres W) (h : A →* A) :
    NoBUP W.C W.D h := by sorry

end BUP
