-- Prove2me | Theorems.Thm_FTheoryK3Tate_budget_exceptional
-- name    : FTheoryK3Tate.budget_exceptional
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T09:56:06.209129+00:00
-- url     : https://prove2.me/theorems/676028aa-5485-4cc3-8c5e-ea280686952b
-- title:
--   budget_exceptional
-- statement:
--   Exceptional-fibre budget. For a characteristic-zero Weierstrass model with $\deg f \le 8$, $\deg g \le 12$, $\Delta \ne 0$, and pairwise-disjoint finite sets $S_6, S_7, S_8$ of base points carrying Kodaira types $\mathrm{IV}^*, \mathrm{III}^*, \mathrm{II}^*$ respectively, $8|S_6| + 9|S_7| + 10|S_8| \le 24$. Geometrically these are the $E_6, E_7, E_8$ loci.
-- source:
--   Kodaira/Tate classification of singular fibres: J. Tate (LNM 476, 1975); M. Schuett, T. Shioda, Elliptic Surfaces, arXiv:0907.0298; F-theory dictionary: T. Weigand, TASI Lectures on F-theory, arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k] [CharZero k]
/-- Corollary (exceptional-fibre budget). For a Calabi–Yau/K3 model, given pairwise-disjoint
    finite sets `S6, S7, S8` of base points carrying types `IV*`, `III*`, `II*` respectively,
    the weighted count is bounded by the discriminant degree:
    `8·|S6| + 9·|S7| + 10·|S8| ≤ 24`. Geometrically these are the `E6`, `E7`, `E8` loci (in the
    split/geometric setting). -/
theorem budget_exceptional (f g : k[X]) (h : IsK3Data f g)
    (S6 S7 S8 : Finset k)
    (d67 : Disjoint S6 S7) (d68 : Disjoint S6 S8) (d78 : Disjoint S7 S8)
    (h6 : ∀ t ∈ S6, HasKodaira f g t Kodaira.IVstar)
    (h7 : ∀ t ∈ S7, HasKodaira f g t Kodaira.IIIstar)
    (h8 : ∀ t ∈ S8, HasKodaira f g t Kodaira.IIstar) :
    8 * S6.card + 9 * S7.card + 10 * S8.card ≤ 24 := by
  sorry
end FTheoryK3Tate
