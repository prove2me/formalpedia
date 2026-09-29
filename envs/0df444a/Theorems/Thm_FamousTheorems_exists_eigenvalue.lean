-- Prove2me | Theorems.Thm_FamousTheorems_exists_eigenvalue
-- name    : FamousTheorems.exists_eigenvalue
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:12:59.200266+00:00
-- url     : https://prove2.me/theorems/fded0c65-b81c-4e0e-9a67-aaa981b0f26b
-- title:
--   Existence of an eigenvalue
-- statement:
--   **Existence of an eigenvalue.** Every endomorphism of a nonzero finite-dimensional space over an algebraically closed field has an eigenvalue, because the characteristic polynomial has positive degree and therefore a root. The statement is the fundamental theorem of algebra transported into linear algebra. Algebraic closure is essential: rotation of the real plane by a right angle has no real eigenvalue, which is why real matrices are studied through their complexifications. This is the first step in every triangularisation argument and in the proof of the Jordan normal form. **Formalization note.** `HasEigenvalue` asserts a nonzero kernel for $f - \mu$. The result is Mathlib's `Module.End.exists_eigenvalue`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_eigenvalue :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] 
    [inst_2 : Module K V] [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : Module.End K V), 
    ∃ c, f.HasEigenvalue c := by sorry

end FamousTheorems
