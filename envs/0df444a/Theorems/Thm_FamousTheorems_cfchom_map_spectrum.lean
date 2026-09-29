-- Prove2me | Theorems.Thm_FamousTheorems_cfchom_map_spectrum
-- name    : FamousTheorems.cfchom_map_spectrum
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:55:18.165652+00:00
-- url     : https://prove2.me/theorems/ae08084b-d0d9-4f40-9fef-103595f82be6
-- title:
--   The spectral mapping theorem
-- statement:
--   **The spectral mapping theorem.** For continuous functional calculus, the spectrum of $f(a)$ is the image of the spectrum of $a$ under $f$: $$\sigma(f(a)) = f(\sigma(a)).$$ Applying a function to an operator applies it to the spectrum, which is what makes functional calculus a genuine calculus rather than formal notation. The consequences are immediate and constant in use: a positive self-adjoint operator has a positive square root with the expected spectrum, the exponential of a self-adjoint operator is unitary, and spectral projections behave as expected. **Formalization note.** `cfcHom` is the continuous functional calculus homomorphism for an element satisfying the relevant predicate. The result is Mathlib's `cfcHom_map_spectrum`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem cfchom_map_spectrum :
    ∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : CommSemiring R] [inst_1 : StarRing R] 
    [inst_2 : MetricSpace R] [inst_3 : IsTopologicalSemiring R] [inst_4 : ContinuousStar R] [inst_5 : TopologicalSpace A] 
    [inst_6 : Ring A] [inst_7 : StarRing A] [inst_8 : Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p] {a : A} 
    (ha : p a) (f : C(↑(spectrum R a), R)), spectrum R ((cfcHom ha) f) = range ⇑f := by sorry

end FamousTheorems
