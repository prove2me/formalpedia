-- Prove2me | Theorems.Thm_BinPacking_Decreasing_bfd_follows_ffd_large_items
-- name    : BinPacking.Decreasing.bfd_follows_ffd_large_items
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:15:27.622146+00:00
-- url     : https://prove2.me/theorems/8150f951-cae8-4857-8211-ecb0d781086c
-- title:
--   Claim 3.4.5 — on $[1/6,1]$, BFD places every element exceeding $1/3$ in its FFD position
-- statement:
--   Let $L$ be a list of real numbers in $[1/6,1]$, and let $a_1\ge a_2\ge\dots\ge a_n$ be $L$ arranged into nonincreasing order. Let $PF$ be the First-Fit Decreasing packing of $L$, and let $f_0(a_i)=(j,k)$ if $a_i$ is the $k$-th element placed into bin $j$ of $PF$ (the $k$-th largest element of that bin, ties broken by the order of the list). Let
--   $$h=\max\{i : a_i>1/3\},$$
--   with $h=0$ if no element exceeds $1/3$.
--
--   Then for every $i$ with $1\le i\le h$, Best-Fit Decreasing places $a_i$ in position $f_0(a_i)$: into the same bin as FFD, as the same (the $k$-th) element of that bin.
--
--   This is the first step of the proof that $BFD(L)\le FFD(L)$ on $[1/6,1]$ (Theorem 3.4): up to the last element exceeding $1/3$, the two decreasing algorithms build identical packings.
--
--   **Formalization Note** The statement is about the sorted list $S=$ `sortDesc L`, on which both FFD and BFD run. Since $S$ is nonincreasing, $h$ is the number of elements of $S$ exceeding $1/3$. Items are $0$-indexed, so the paper's $1\le i\le h$ is `i < h`; the position of item `i` is given by `binOf` (the bin) and `slotOf` (how many elements the bin held when item `i` arrived), for the FF run and the BF run on $S$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 312, Claim 3.4.5 (with h defined just before it; f₀ defined p. 310)

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- Claim 3.4.5 (p. 312), stated on `S = sortDesc L` for `L ⊆ [1/6, 1]`: with `h` the number
of elements of `S` exceeding `1/3` (the paper's `h = max {i : a_i > 1/3}`, `0` if none, for
the nonincreasing list `S`), each of the first `h` items is placed by BFD in the position it
fills in the FFD packing: the same bin, at the same place within the bin. -/
theorem bfd_follows_ffd_large_items (L : List ℝ) (hL : IsList L)
    (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) (i : Fin (sortDesc L).length)
    (hi : (i : ℕ) < ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length) :
    binOf bfChoice (sortDesc L) i = binOf ffChoice (sortDesc L) i ∧
      slotOf bfChoice (sortDesc L) i = slotOf ffChoice (sortDesc L) i := by sorry

end BinPacking.Decreasing
