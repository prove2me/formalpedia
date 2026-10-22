-- Prove2me | Theorems.Thm_BUP_tau1_witness
-- name    : BUP.tau1_witness
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:28:02.714065+00:00
-- url     : https://prove2.me/theorems/3d61611b-dbbb-4932-8ccc-5732f5ee0024
-- title:
--   The algebraic witness criterion for the orientation-preserving involution of the torus (Lemma 26)
-- statement:
--   In the torus world, the homotopy class with induced homomorphism h does not have the Borsuk-Ulam property if and only if there are pure braids a and b such that the half-twist conjugation relation holds - a times the conjugate of b equals b times a - and the image of the first coordinate loop under h is the Fadell-Neuwirth projection of a times the conjugate of a, while the image of the second coordinate loop under h is the projection of b. The criterion unwinds the diagram of Proposition 6 along the decomposition of the full two-string braid group of the torus into the pure braid group and the half-twist.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 5 (Lemma 26).

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor

namespace BUP

/-!  Milestone 4 (Lemma 26): the algebraic witness criterion for the
orientation-preserving involution of the torus. The homotopy class with
induced homomorphism h does not have the Borsuk-Ulam property if and only if
there are pure braids a and b such that a conjugated by the half-twist
commutation relation holds (a times the conjugate of b equals b times a), the
image of the first coordinate loop under h is the Fadell-Neuwirth projection
of a times the conjugate of a, and the image of the second coordinate loop
under h is the projection of b. The proof unwinds the diagram of Proposition 6
along the decomposition of the full braid group into the pure braid group and
the half-twist. -/
theorem tau1_witness {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (h : A →* A) :
    NoBUP W.C W.D h ↔
      ∃ a b : P,
        a * W.D.lsigma b = b * a ∧
        h (W.e1) = W.D.p1 (a * W.D.lsigma a) ∧
        h (W.e2) = W.D.p1 b := by sorry

end BUP
