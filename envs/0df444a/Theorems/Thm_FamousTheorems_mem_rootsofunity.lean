-- Prove2me | Theorems.Thm_FamousTheorems_mem_rootsofunity
-- name    : FamousTheorems.mem_rootsofunity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:40.960988+00:00
-- url     : https://prove2.me/theorems/f36322ad-2a9e-46c2-9d05-16dd9fa53851
-- title:
--   Complex roots of unity
-- statement:
--   **The complex $n$-th roots of unity.** A unit $x \in \mathbb{C}^\times$ satisfies $x^n = 1$ if and only if $$x = e^{2\pi i\,k/n}\quad\text{for some } 0 \le k < n.$$ The $n$-th roots of unity are exactly the $n$ points equally spaced around the unit circle starting at $1$. They form a cyclic group of order $n$ under multiplication — the unique such subgroup of $\mathbb{C}^\times$ — and geometrically they are the vertices of a regular $n$-gon inscribed in the unit circle. This explicit description is what connects the algebra of cyclotomic fields to the geometry of regular polygons, and hence to Gauss's criterion for constructibility by ruler and compass. The sum of all $n$-th roots of unity is zero for $n > 1$, which is the orthogonality relation underlying the discrete Fourier transform. **Formalization note.** `rootsOfUnity n ℂ` is the subgroup of $\mathbb{C}^\times$ of elements killed by $n$, and `NeZero n` excludes the degenerate case. The result is Mathlib's `Complex.mem_rootsOfUnity`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem mem_rootsofunity :
    ∀ (n : ℕ) [NeZero n] (x : ℂˣ), 
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < n, Complex.exp (2 * ↑Real.pi * Complex.I * (↑i / ↑n)) = ↑x := by sorry

end FamousTheorems
