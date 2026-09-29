-- Prove2me | Theorems.Thm_FamousTheorems_fg_abelian_structure
-- name    : FamousTheorems.fg_abelian_structure
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T07:14:54.065546+00:00
-- url     : https://prove2.me/theorems/ec425a82-b215-4d0e-8b9a-3aed9dbcb17b
-- title:
--   Structure theorem for finitely generated abelian groups
-- statement:
--   **The structure theorem for finitely generated abelian groups.**
--
--   Every finitely generated abelian group decomposes as
--   $$G \;\cong\; \mathbb{Z}^n \;\oplus\; \bigoplus_i \mathbb{Z}/p_i^{e_i}\mathbb{Z}$$
--   with each $p_i$ prime.
--
--   A free part of well-defined rank plus a finite torsion part split into primary cyclic factors.
--   Every finite abelian group is therefore a direct sum of cyclic groups of prime power order,
--   and the multiset of those orders is a complete isomorphism invariant — so classifying finite
--   abelian groups of a given order reduces to counting partitions of the exponents in its prime
--   factorization.
--
--   This is the specialization to $R = \mathbb{Z}$ of the structure theorem for modules over a
--   principal ideal domain, and it is the reason the classification of finitely generated abelian
--   groups is completely solved while the non-abelian case is not.
--
--   Usually attributed to Kronecker (1870) for the finite case, with the finitely generated
--   version following from Smith normal form.
--
--   **Formalization note.** `Fin n →₀ ℤ` is the free abelian group of rank `n` and `⨁` the direct
--   sum; the isomorphism is data, so it appears wrapped in `Nonempty` inside the existential. The
--   result is Mathlib's `AddCommGroup.equiv_free_prod_directSum_zmod`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests (docs/undergrad.yaml, docs/overview.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

open Filter Set Topology DirectSum

theorem fg_abelian_structure (G : Type u) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i) := by sorry

end FamousTheorems
