-- Prove2me | Theorems.Thm_FamousTheorems_stars_and_bars_theorem
-- name    : FamousTheorems.stars_and_bars_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:34.567994+00:00
-- url     : https://prove2.me/theorems/7e1e3cae-fa5a-4abf-b6f0-dcb63e044eb7
-- title:
--   Stars and bars
-- statement:
--   **Stars and bars.** Let $\alpha$ be a finite set with $n$ elements and let $k\in\mathbb N$. The number of multisets of size $k$ with elements from $\alpha$ is
--   $$\left(\!\!\binom{n}{k}\!\!\right)=\binom{n+k-1}{k}.$$
--
--   Equivalently, this is the number of ways to put $k$ identical balls into $n$ distinguishable boxes, or the number of solutions of $x_1+\cdots+x_n=k$ in non-negative integers. It is one of the basic counting principles of enumerative combinatorics (the twelvefold way). It also gives the dimension of the space of degree-$k$ homogeneous polynomials in $n$ variables.
--
--   **Formalization note.** Mathlib's `Sym.card_sym_eq_multichoose`. `Sym α k` is the type of multisets of size $k$ over $\alpha$, and `Nat.multichoose n k` is the multiset coefficient, equal to $\binom{n+k-1}{k}$ (Mathlib's `Nat.multichoose_eq`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Sym.card_sym_eq_multichoose`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem stars_and_bars_theorem (α : Type*) (k : ℕ) [Fintype α] [DecidableEq α] :
    Fintype.card (Sym α k) = (Fintype.card α).multichoose k := by sorry

end FamousTheorems
