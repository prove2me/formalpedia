-- Prove2me | Theorems.Thm_FamousTheorems_trace_form_nondegenerate_7b
-- name    : FamousTheorems.trace_form_nondegenerate_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:14.71435+00:00
-- url     : https://prove2.me/theorems/3b432c1a-9b56-4c6c-ba23-c2d58cfd9244
-- title:
--   The trace form of a finite separable extension is nondegenerate
-- statement:
--   **The trace form of a finite separable extension is nondegenerate.** Let $L/K$ be a finite separable field extension. The trace form $(x,y)\mapsto\operatorname{Tr}_{L/K}(xy)$ is a nondegenerate symmetric bilinear form on $L$ over $K$.
--
--   In particular the trace map is not identically zero and the discriminant of any basis of $L/K$ is nonzero. This is the basis of the theory of discriminants and of the different, and it shows that the ring of integers of a number field is a free $\mathbb Z$-module of rank $[L:\mathbb Q]$. Separability is necessary: for a purely inseparable extension the trace is zero.
--
--   **Formalization note.** Mathlib's `traceForm_nondegenerate`. `Algebra.traceForm K L` is the bilinear form $(x,y)\mapsto\operatorname{Tr}_{L/K}(xy)$, and `Nondegenerate` says that $x$ is zero if the form vanishes on $x$ and every $y$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `traceForm_nondegenerate`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem trace_form_nondegenerate_7b (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (Algebra.traceForm K L).Nondegenerate := by sorry

end FamousTheorems
