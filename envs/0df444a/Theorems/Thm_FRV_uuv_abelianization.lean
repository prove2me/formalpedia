-- Prove2me | Theorems.Thm_FRV_uuv_abelianization
-- name    : FRV.uuv_abelianization
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:12:02.546864+00:00
-- url     : https://prove2.me/theorems/cbcbdd99-a80f-4175-9e94-f72a27a9e24a
-- title:
--   The abelianization of the unrestricted group: the free part and the order-two part (Proposition 4.6)
-- statement:
--   The abelianization of the universal unrestricted virtual braid group is the direct sum of the free Abelian group of rank k with the cyclic group of order two. All virtual generators of a given family share one class in the abelianization, all sigma generators of a given type share one free class, and the forbidden relations impose no additional relation on the abelianization beyond the order-two identification of the virtual class. This is Proposition 4.6 of the paper.
-- source:
--   O. Ocampo, C. Stylianakis, Forbidden relations in universal virtual braid groups, arXiv:2606.06095 (2026), Section 4 (Proposition 4.6).

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

namespace FRV

/-!  Milestone 7 (Proposition 4.6): the abelianization of the universal
unrestricted virtual braid group is the direct sum of the free Abelian
group of rank k with the cyclic group of order two. All virtual generators
of a given family share one class in the abelianization, all sigma
generators of a given type share one free class, and the forbidden
relations impose no additional relation on the abelianization. -/
theorem uuv_abelianization {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type*}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) (hn : 3 ≤ n) :
    ∃ ab : U →* Multiplicative ((Fin k → ℤ) × ZMod 2),
      (∀ y : Multiplicative ((Fin k → ℤ) × ZMod 2), ∃ x : U, ab x = y) ∧
      MonoidHom.ker ab = Derived U := by sorry

end FRV
