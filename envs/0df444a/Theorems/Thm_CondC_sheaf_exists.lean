-- Prove2me | Theorems.Thm_CondC_sheaf_exists
-- name    : CondC.sheaf_exists
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T15:50:50.946718+00:00
-- url     : https://prove2.me/theorems/9130a9ff-29b2-4c0f-9e7a-5c21508b4208
-- title:
--   The sheaf of holomorphic functions (Theorems 1.1 and 5.1)
-- statement:
--   Theorem 1.1 of the introduction, proved as Theorem 5.1: there is a necessarily unique sheaf O on the complex plane such that on each open disc D(x, r) the sections identify with the power series in (T - x) whose coefficients satisfy the decay condition, with transition maps compatible with evaluation at points; and the higher sheaf cohomology of each disc vanishes. The milestone states existence and uniqueness: there is a disc presheaf carrying the power-series identification and satisfying the two-disc sheaf condition; and any two such are uniquely isomorphic, by an isomorphism compatible with the restriction maps and with the power-series identifications.
--
--   **Formalization Note** The sheaf condition is stated in the two-disc form that the paper's proof uses: sections agreeing on every disc contained in the overlap of a two-disc cover glue uniquely. The uniqueness of the sheaf is stated up to restriction-compatible, identification-compatible isomorphism. The acyclicity half is the next milestone.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (May 2026 version), Lectures I and V (Theorems 1.1 and 5.1).

import Mathlib
import Definitions.Def_CondC_liq
import Definitions.Def_CondC_geo

namespace CondC

/-!  Milestone 3: the sheaf of holomorphic functions. There is a disc
presheaf carrying the power-series identification of Theorem 5.1 and
satisfying the two-disc sheaf condition; and any two such are uniquely
isomorphic, by an isomorphism compatible with restriction and with the
power-series identifications. This is the existence and uniqueness of the
structure sheaf O (Theorems 1.1 and 5.1).  -/
theorem sheaf_exists : ∃ (P : DiscModulePresheaf) (O : OIdentification P),
    SheafGlue2 P ∧
    ∀ (Q : DiscModulePresheaf) (O' : OIdentification Q), SheafGlue2 Q →
      ∃! e : (d : Disc) → P.F d ≃ Q.F d,
        (∀ (d d' : Disc) (h : SubDisc d d') (s : P.F d'),
          Q.res d d' h (e d' s) = e d (P.res d d' h s)) ∧
        (∀ (d : Disc) (s : P.F d), O.coeffs d s = O'.coeffs d (e d s)) := by sorry

end CondC
