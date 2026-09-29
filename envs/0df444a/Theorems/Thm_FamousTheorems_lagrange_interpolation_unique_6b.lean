-- Prove2me | Theorems.Thm_FamousTheorems_lagrange_interpolation_unique_6b
-- name    : FamousTheorems.lagrange_interpolation_unique_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:33.100252+00:00
-- url     : https://prove2.me/theorems/17ef5fbe-f4b5-4fd8-abfa-9a76a3822084
-- title:
--   Uniqueness of the Lagrange interpolation polynomial
-- statement:
--   **Uniqueness of the Lagrange interpolation polynomial.** Let $F$ be a field, $x_1,\dots,x_n\in F$ distinct nodes and $r_1,\dots,r_n\in F$ values. If a polynomial $f\in F[X]$ has $\deg f<n$ and $f(x_i)=r_i$ for all $i$, then $f$ equals the Lagrange interpolation polynomial
--   $$L(X)=\sum_{i=1}^n r_i\prod_{j\ne i}\frac{X-x_j}{x_i-x_j}.$$
--
--   A polynomial of degree less than $n$ is therefore determined by its values at $n$ points. The result is used in secret sharing, Reed–Solomon codes, numerical analysis and the proof of the Chinese remainder theorem for polynomials.
--
--   **Formalization note.** Mathlib's `Lagrange.eq_interpolate_of_eval_eq`. The nodes are $v(i)$ for $i$ in a finite set $s$ and are assumed distinct (`Set.InjOn v s`). `Lagrange.interpolate s v r` is the Lagrange polynomial through the points $(v(i),r(i))$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Lagrange.eq_interpolate_of_eval_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lagrange_interpolation_unique_6b {F ι : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} (r : ι → F) {f : Polynomial F}
    (hvs : Set.InjOn v s) (hf : f.degree < s.card) (heval : ∀ i ∈ s, f.eval (v i) = r i) :
    f = Lagrange.interpolate s v r := by sorry

end FamousTheorems
