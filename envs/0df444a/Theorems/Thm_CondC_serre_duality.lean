-- Prove2me | Theorems.Thm_CondC_serre_duality
-- name    : CondC.serre_duality
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T15:52:28.171274+00:00
-- url     : https://prove2.me/theorems/8017dc61-01b9-4a99-a75f-cbc1d64196bc
-- title:
--   Serre duality (Theorem 13.6)
-- statement:
--   Theorem 13.6 of the paper: for a d-dimensional smooth map f : X to Y, there is a natural isomorphism f!M = f*M tensor Omega^d[d]. Over the point base this is the classical Serre duality: the dual of H^i(X, F) identifies with H^(d-i)(X, the dual of F tensored with Omega^d). The milestone states the point case in pairing form: for a coherent coefficient on a compact complex world of dimension d and every degree i at most d, there is a pairing between the degree d - i group of the dualizing coefficient and the degree i group of the coefficient, bilinear in both arguments, nondegenerate in both arguments, and exhaustive: every linear functional on the degree i group is the pairing against some vector of the dual group.
--
--   **Formalization Note** The dualizing complex Omega^d[d] is absorbed into the abstract dualizing coefficient data of the world; the relative form of Theorem 13.6 and the derived equivalence behind it are the proposed work of the milestone.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (May 2026 version), Lectures I and XIII (Theorem 13.6, the point case).

import Mathlib
import Definitions.Def_CondC_liq
import Definitions.Def_CondC_geo

namespace CondC

/-!  Milestone 6: Serre duality (Theorem 13.6, the point case). For a
coherent coefficient on a compact complex manifold of dimension d, there is
a pairing between the degree d - i group of the dualizing data and the
degree i group of the coefficient, bilinear in both arguments, nondegenerate
in both arguments, and exhaustive: every linear functional on the degree i
group is the pairing against some vector of the dual group.  -/
theorem serre_duality : ∀ (w : CompactCxWorld) (F : Type), w.coherent F →
    ∃ pair : (i : ℕ) → i ≤ w.dim → w.Coh (w.dualF F) (w.dim - i) → w.Coh F i → ℂ,
      (∀ (i : ℕ) (hi : i ≤ w.dim) (x y : w.Coh (w.dualF F) (w.dim - i))
          (z : w.Coh F i),
        pair i hi (w.add (w.dualF F) (w.dim - i) x y) z
          = pair i hi x z + pair i hi y z) ∧
      (∀ (i : ℕ) (hi : i ≤ w.dim) (k : ℂ) (x : w.Coh (w.dualF F) (w.dim - i))
          (z : w.Coh F i),
        pair i hi (w.smul (w.dualF F) (w.dim - i) k x) z = k * pair i hi x z) ∧
      (∀ (i : ℕ) (hi : i ≤ w.dim) (x : w.Coh (w.dualF F) (w.dim - i))
          (y z : w.Coh F i),
        pair i hi x (w.add F i y z) = pair i hi x y + pair i hi x z) ∧
      (∀ (i : ℕ) (hi : i ≤ w.dim) (k : ℂ) (x : w.Coh (w.dualF F) (w.dim - i))
          (z : w.Coh F i),
        pair i hi x (w.smul F i k z) = k * pair i hi x z) ∧
      (∀ (i : ℕ) (hi : i ≤ w.dim) (x : w.Coh (w.dualF F) (w.dim - i)),
        (∀ z : w.Coh F i, pair i hi x z = 0) → x = w.zero (w.dualF F) (w.dim - i)) ∧
      (∀ (i : ℕ) (hi : i ≤ w.dim) (z : w.Coh F i),
        (∀ x : w.Coh (w.dualF F) (w.dim - i), pair i hi x z = 0) → z = w.zero F i) ∧
      (∀ (i : ℕ) (hi : i ≤ w.dim)
          (φ : BundledLinearMap (w.Coh F i) ℂ (w.add F i) (w.zero F i) (w.smul F i)
            (fun x y => x + y) (0 : ℂ) (fun k x => k * x)),
        ∃ u : w.Coh (w.dualF F) (w.dim - i), ∀ z : w.Coh F i, pair i hi u z = φ.map z)
    := by sorry

end CondC
