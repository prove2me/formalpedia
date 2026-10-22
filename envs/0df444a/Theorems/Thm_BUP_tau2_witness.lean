-- Prove2me | Theorems.Thm_BUP_tau2_witness
-- name    : BUP.tau2_witness
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:28:40.516463+00:00
-- url     : https://prove2.me/theorems/ec070987-4dfd-40b2-8bed-bd23a2c517a2
-- title:
--   The algebraic witness criterion for the orientation-reversing involution of the torus (Lemma 28)
-- statement:
--   In the torus world of the orientation-reversing free involution, the homotopy class with induced homomorphism h does not have the Borsuk-Ulam property if and only if there are pure braids a and b with the relation a times b times the conjugate of a equals b, such that the image of the first coordinate loop under h is the Fadell-Neuwirth projection of a, and the image of the second coordinate loop under h is the projection of b times the conjugate of b. The criterion follows the pattern of Lemma 26 with the homomorphisms adapted to the deck sequence of the orientation-reversing involution, whose orbit space is the Klein bottle.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 5 (Lemma 28).

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor

namespace BUP

/-!  Milestone 5 (Lemma 28): the algebraic witness criterion for the
orientation-reversing involution of the torus. The homotopy class with induced
homomorphism h does not have the Borsuk-Ulam property if and only if there are
pure braids a and b with the relation a times b times the conjugate of a
equals b, such that the image of the first coordinate loop under h is the
Fadell-Neuwirth projection of a, and the image of the second coordinate loop
under h is the projection of b times the conjugate of b. The proof follows
Lemma 26 with the homomorphisms adapted to the deck sequence of the
orientation-reversing involution, whose orbit space is the Klein bottle. -/
theorem tau2_witness {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (h : A →* A) :
    NoBUP W.C W.D h ↔
      ∃ a b : P,
        a * b * W.D.lsigma a = b ∧
        h (W.e1) = W.D.p1 a ∧
        h (W.e2) = W.D.p1 (b * W.D.lsigma b) := by sorry

end BUP
