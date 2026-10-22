-- Prove2me | Theorems.Thm_BUP_involution_inequiv
-- name    : BUP.involution_inequiv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:27:22.787089+00:00
-- url     : https://prove2.me/theorems/ee9ee97f-5ecc-4eac-bfeb-3ae4fb6bc9e2
-- title:
--   The orientation-preserving and orientation-reversing free involutions of the torus are inequivalent (Proposition 25, first part)
-- statement:
--   If the orbit group of the first torus world is Abelian - as it is for the orientation-preserving free involution, whose orbit space is the torus - and the orbit group of the second is not - as it is for the orientation-reversing involution, whose orbit space is the Klein bottle - then there are no isomorphisms of the surface groups and the orbit groups compatible with the covering injections and the deck projections between the two worlds. By Proposition 10 the induced short exact sequences, and hence the two free involutions, are inequivalent: the free involutions of the torus fall into exactly two classes.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 5 (Proposition 25, first part, with Proposition 10).

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor

namespace BUP

/-!  Milestone 3 (Proposition 25, first part): the orientation-preserving and
the orientation-reversing free involutions of the torus are not equivalent. In
the interface: if the orbit group of the first torus world is Abelian - as for
the orientation-preserving involution, whose orbit space is the torus - and
the orbit group of the second is not - as for the orientation-reversing
involution, whose orbit space is the Klein bottle - then there are no
isomorphisms of the surface groups and the orbit groups compatible with the
covering injections and the deck projections; by Proposition 10 the induced
short exact sequences are inequivalent, and so are the involutions. -/
theorem involution_inequiv {A1 B1 P1 Bg1 A2 B2 P2 Bg2 : Type*} [Group A1] [Group B1] [Group P1]
    [Group Bg1] [Group A2] [Group B2] [Group P2] [Group Bg2]
    (W1 : TorusWorld A1 B1 P1 Bg1) (W2 : TorusWorld A2 B2 P2 Bg2)
    (hab : ∀ x y : B1, x * y = y * x)
    (hnb : ∃ x y : B2, x * y ≠ y * x) :
    ¬ (∃ eA : A1 ≃* A2, ∃ eB : B1 ≃* B2,
      (∀ a : A1, eB (W1.C.inj a) = W2.C.inj (eA a)) ∧
      (∀ b : B1, W2.C.proj (eB b) = W1.C.proj b)) := by sorry

end BUP
