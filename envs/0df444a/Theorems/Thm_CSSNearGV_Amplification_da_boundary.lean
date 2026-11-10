-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_da_boundary
-- name    : CSSNearGV.Amplification.da_boundary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:48.544187+00:00
-- url     : https://prove2.me/theorems/8c1ca1a7-483f-423b-a84d-a09051d19849
-- title:
--   Theorem 5.8 — DA boundary induction
-- statement:
--   For fixed even $s\ge2$, let $T=(\log n)^2$ and $B_T=([1,T)\cup(n-T,n])\cap\mathbb Z$. For $m\ge1$,
--   $$\sum_{c\in B_T}W_{DA}^{(m)}(c)=\widetilde O(n^{-m}).$$
--   Consequently, for $m\ge2$, the expected number of nonzero words having weight below $\tau n$ or above $(1-\tau)n$ after $m-1$ rounds is $\widetilde O(n^{1-m})$. Both clauses are included. These estimates control the penultimate boundary contribution.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: poly(n), soft-O and negligible estimates → eventual inequalities with positive constants, exponents and thresholds fixed before length and all weights; reason: the source leaves numerical prefactors unspecified; parameters s, m and epsilon are fixed before these constants
--   - reading: unbased log in the boundary cutoff → natural logarithm in T=(log n)^2; reason: the source leaves this base unstated; a fixed base changes the cutoff by a constant factor, and the boundary and negligible estimates retain their stated orders
--   - encoding: expected boundary count after m-1 rounds in an m-round ensemble → boundaryCount at round m-1; reason: discarding the last two independent uniform permutations leaves exactly the (m-1)-round product law; the final round is bijective and preserves the number of tracked words
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Theorem 5.8, printed p.20 / PDF 22

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem da_boundary (s : ℕ) (hs : 2 ≤ s) (he : Even s) :
  (∀ m : ℕ, 1 ≤ m → SoftBound s (fun b => boundaryCount s b m false) (-(m : ℝ))) ∧
  (∀ m : ℕ, 2 ≤ m → SoftBound s (fun b => boundaryCount s b (m - 1) false) (1 - (m : ℝ))) := by sorry

end CSSNearGV.Amplification
