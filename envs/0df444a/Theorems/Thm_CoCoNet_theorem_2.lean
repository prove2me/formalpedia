-- Prove2me | Theorems.Thm_CoCoNet_theorem_2
-- name    : CoCoNet.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:19.481987+00:00
-- url     : https://prove2.me/theorems/297afc87-3156-4be6-8c28-11c2d99d72c6
-- title:
--   Theorem 2 — Poincaré–Miranda theorem on $[-1,1]^n$
-- statement:
--   For $i\in[n]$ let $U_i=\{u\in[-1,1]^n : u_i=1\}$ and $U_{-i}=\{u\in[-1,1]^n : u_i=-1\}$ be the opposite faces of the cube. Let $F:[-1,1]^n\to\mathbb R^n$ be continuous and suppose that for every $i$,
--   $$u\in U_i\ \Rightarrow\ F_i(u)\ge 0,\qquad u\in U_{-i}\ \Rightarrow\ F_i(u)\le 0.$$
--   Then there is $w\in[-1,1]^n$ with $F_i(w)=0$ for all $i$.
--
--   This is the paper's tool for the existence part of the fair case (via Proposition 2); it is quoted from Browder (1983) and is equivalent to Brouwer's fixed point theorem.
--
--   **Formalization Note** The cube is `Set.Icc (-1) 1` in `Fin n → ℝ`.
--
--   Differences from the source:
--   - encoding: F : [−1, 1]ⁿ → ℝⁿ continuous → F : (Fin n → ℝ) → (Fin n → ℝ) with ContinuousOn F on the cube; reason: only the values on the cube enter; every function on the cube extends to ℝⁿ
--   - encoding: indices [n] = {1, …, n}; vectors in ℝⁿ → indices Fin n (0-based); vectors Fin n → ℝ; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Theorem 2 (Poincaré–Miranda), p.30

import Mathlib

namespace CoCoNet

/-- **Theorem 2 (Poincaré–Miranda).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Theorem 2, p.30 (quoted from Browder 1983): "Define
Uᵢ = {u ∈ [−1, 1]ⁿ | uᵢ = 1} and U₋ᵢ = {u ∈ [−1, 1]ⁿ | uᵢ = −1}. Let F : [−1, 1]ⁿ → ℝⁿ be a
continuous function with the property that for all i ∈ [n] u ∈ Uᵢ implies Fᵢ(u) ≥ 0 and u ∈ U₋ᵢ
implies Fᵢ(u) ≤ 0. Then there exists w ∈ [−1, 1]ⁿ such that Fᵢ(w) = 0 for all i ∈ [n]."

**Formalization Note.** The cube `[−1, 1]ⁿ` is `Set.Icc (-1) 1` in `Fin n → ℝ`. `F` is given on
all of `ℝⁿ`, but only its values on the cube enter (`ContinuousOn` and the boundary
conditions). -/
theorem theorem_2 {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContinuousOn F (Set.Icc (-1) 1))
    (hpos : ∀ i, ∀ u ∈ Set.Icc (-1 : Fin n → ℝ) 1, u i = 1 → 0 ≤ F u i)
    (hneg : ∀ i, ∀ u ∈ Set.Icc (-1 : Fin n → ℝ) 1, u i = -1 → F u i ≤ 0) :
    ∃ w ∈ Set.Icc (-1 : Fin n → ℝ) 1, ∀ i, F w i = 0 := by sorry

end CoCoNet
