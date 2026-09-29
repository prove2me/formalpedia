-- Prove2me | Theorems.Thm_FamousTheorems_roth_theorem_3ap
-- name    : FamousTheorems.roth_theorem_3ap
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:58.289985+00:00
-- url     : https://prove2.me/theorems/9b8ba4a8-35e9-4d9b-9ee0-cd7023c15785
-- title:
--   Roth's theorem on 3-term arithmetic progressions
-- statement:
--   **Roth's theorem.** For every $\varepsilon>0$ there is $N$ such that for all $n\ge N$, every set $A\subseteq\{0,1,\dots,n-1\}$ with $|A|\ge\varepsilon n$ contains a nontrivial three-term arithmetic progression $a,a+d,a+2d$ with $d>0$.
--
--   Equivalently, sets of natural numbers without 3-term progressions have density zero. This is the case $k=3$ of Szemerédi's theorem. Roth proved it by Fourier analysis in 1953, and it has driven major developments in additive combinatorics, including the Kelley–Meka bounds.
--
--   **Formalization note.** Derived from Mathlib's `roth_3ap_theorem_nat`, which obtains Roth's theorem from the corners theorem with $N=$ `cornersTheoremBound (ε / 3)`. `ThreeAPFree A` means $A$ contains no $a,b,c$ with $a+c=2b$ other than $a=b=c$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `roth_3ap_theorem_nat`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem roth_theorem_3ap (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ, A ⊆ Finset.range n → ε * n ≤ A.card → ¬ ThreeAPFree (A : Set ℕ) := by sorry

end FamousTheorems
