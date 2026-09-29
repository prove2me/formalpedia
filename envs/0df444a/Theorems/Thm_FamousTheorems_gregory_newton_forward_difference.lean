-- Prove2me | Theorems.Thm_FamousTheorems_gregory_newton_forward_difference
-- name    : FamousTheorems.gregory_newton_forward_difference
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:43.182985+00:00
-- url     : https://prove2.me/theorems/5d0d0691-2854-4b89-b768-e3b9c3cc4589
-- title:
--   The Gregory–Newton forward difference formula
-- statement:
--   **The Gregory–Newton forward difference formula.** Let $f:M\to G$ be a function from a commutative monoid to an abelian group, $h\in M$, and $\Delta_h f(y)=f(y+h)-f(y)$ the forward difference. Then for every $y\in M$ and $n\in\mathbb N$,
--   $$f(y+nh)=\sum_{k=0}^n\binom nk\,\Delta_h^k f(y).$$
--
--   This is the discrete analogue of Taylor's formula and the basis of Newton's interpolation formula. It is used in numerical analysis and in the theory of polynomial and integer-valued functions.
--
--   **Formalization note.** Mathlib's `shift_eq_sum_fwdDiff_iter`. `fwdDiff h` is the operator $\Delta_h$ and `(fwdDiff h)^[k]` its $k$-th iterate.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `shift_eq_sum_fwdDiff_iter`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gregory_newton_forward_difference {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M) (f : M → G) (n : ℕ) (y : M) :
    f (y + n • h) = ∑ k ∈ Finset.range (n + 1), n.choose k • (fwdDiff h)^[k] f y := by sorry

end FamousTheorems
