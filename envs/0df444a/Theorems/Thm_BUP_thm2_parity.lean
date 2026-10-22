-- Prove2me | Theorems.Thm_BUP_thm2_parity
-- name    : BUP.thm2_parity
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:29:45.169848+00:00
-- url     : https://prove2.me/theorems/da96de3c-7b12-4183-9b4c-04218122190d
-- title:
--   The parity classification of the Borsuk-Ulam classes for the orientation-reversing involution of the torus (Theorem 2)
-- statement:
--   In the idealized torus world whose deck transformation reverses orientation - fixing the first integral coordinate and flipping the second - the homotopy class with induced homomorphism h does not have the Borsuk-Ulam property if and only if it is not the case that the first column of the integral matrix of h is nonzero while both entries of the second column are even. Equivalently, the class has the Borsuk-Ulam property exactly when the first column of the matrix is nonzero and both entries of the second column are even, which is the parity classification of Theorem 2. The proof combines the explicit witnesses of Proposition 29 with the palindrome parity analysis of Proposition 32.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 5 (Theorem 2, from Propositions 29 and 32).

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor

namespace BUP

/-!  Milestone 7 (Theorem 2, from Propositions 29 and 32): the classification
of the homotopy classes of selfmaps of the torus that have the Borsuk-Ulam
property with respect to the orientation-reversing free involution. In the
idealized torus world whose deck transformation flips the second integral
coordinate, the class with induced homomorphism h does not have the Borsuk-Ulam
property if and only if it is not the case that the first column of the
integral matrix of h is nonzero while both entries of the second column are
even. The proof combines the explicit witnesses of Proposition 29 with the
palindrome parity analysis of Lemmas 30 and 31 used in Proposition 32. -/
theorem thm2_parity {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (hr : TorusRev W) (h : A →* A) :
    NoBUP W.C W.D h ↔
      ¬ ((W.beta11 h, W.beta21 h) ≠ ((0, 0) : Int × Int) ∧
        Even (W.beta12 h) ∧ Even (W.beta22 h)) := by sorry

end BUP
