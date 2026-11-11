-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_lemma_6_2
-- name    : EntAssistOneWay.Separation.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:57.971817+00:00
-- url     : https://prove2.me/theorems/b467a476-808e-479b-8936-fa926caffa11
-- title:
--   Lemma 6.2 — the exact Heisenberg representation dimension
-- statement:
--   Let $m\ge1$ and let $\zeta=(0,0,1)$ in $H_m(\mathbb F_3)$. Both of the following hold:
--   $$\forall d<3^m\ \forall\rho:H_m\to\operatorname{GL}_d(\mathbb C),\quad\rho(\zeta)=I;\qquad\exists\rho:H_m\to\operatorname{GL}_{3^m}(\mathbb C),\quad\rho(\zeta)\ne I.$$
--   Thus the least dimension of an irreducible representation nontrivial on $\zeta$ is exactly $3^m$. Both the universal lower-dimensional clause and the representation witnessing equality are included. This supplies the exact dimension parameter used for the group family.
--
--   Differences from the source:
--   - encoding: D(Hm,ζ) = 3^m for the least dimension of a unitary irrep → all representations below 3^m kill ζ, and one representation at dimension 3^m does not; reason: finite-group representations are unitarisable and completely reducible, making the conjunction equivalent to the least-irrep equality
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 37, Lemma 6.2; p. 38, proof

import Definitions.Def_EntAssistOneWay_Separation_Heisenberg

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Lemma 6.2, p. 37: both directions of the least-dimension equality. -/
theorem lemma_6_2 (m : ℕ) (hm : 1 ≤ m) :
    DimensionGap (heisenbergZeta m) (3 ^ m) ∧
      ∃ ρ : Heisenberg m →* Matrix.GeneralLinearGroup (Fin (3 ^ m)) ℂ,
        ρ (heisenbergZeta m) ≠ 1 := by sorry

end

end EntAssistOneWay.Separation
