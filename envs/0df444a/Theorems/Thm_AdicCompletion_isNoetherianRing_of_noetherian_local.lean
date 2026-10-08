-- Prove2me | Theorems.Thm_AdicCompletion_isNoetherianRing_of_noetherian_local
-- name    : AdicCompletion.isNoetherianRing_of_noetherian_local
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-04T16:20:45.233752+00:00
-- url     : https://prove2.me/theorems/d994e398-05de-4707-bdce-2bfccfa43ddf
-- title:
--   The completion of a Noetherian local ring is Noetherian
-- statement:
--   Let $(R,\mathfrak m)$ be a commutative Noetherian local ring. Its maximal-ideal-adic completion is Noetherian:
--   $$
--   \widehat R=\varprojlim_{n\geq1} R/\mathfrak m^n
--   \quad\text{is a Noetherian ring}.
--   $$
--
--   This is the local maximal-ideal case of the Noetherianity theorem for ideal-adic completions, a basic input for local dimension and regularity arguments.
--
--   **Formalization Note.** The complete Lean proof establishes Noetherianity for completion at every ideal of every commutative Noetherian ring, then specializes to the maximal ideal. It constructs evaluation from a finite-variable power-series ring, proves surjectivity by adic lifting from the quotient modulo the ideal, and applies Noetherianity of power-series rings and of surjective images. The standalone proof imports only Mathlib and has no Open dependencies. All original hypotheses and the formal statement are unchanged.
-- source:
--   Stacks Project, Lemma 10.97.6, Tag 0316, https://stacks.math.columbia.edu/tag/0316 . Exact specialization of the stated theorem to I equal to the maximal ideal of a Noetherian local ring. The source proves the more general theorem for every ideal of every Noetherian ring.

import Mathlib.RingTheory.AdicCompletion.LocalRing
set_option autoImplicit false

namespace AdicCompletion

theorem isNoetherianRing_of_noetherian_local
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by sorry

end AdicCompletion
