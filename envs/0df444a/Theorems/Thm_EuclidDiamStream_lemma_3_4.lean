-- Prove2me | Theorems.Thm_EuclidDiamStream_lemma_3_4
-- name    : EuclidDiamStream.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:15.335214+00:00
-- url     : https://prove2.me/theorems/dc5ddac5-56cb-4b2c-9f5a-f25a28a9d6a4
-- title:
--   Lemma 3.4 (Main Lemma) — ball-subspace-evasion requires $s=\exp(\Omega(\tau^2/d))$
-- statement:
--   Let $\delta\in(0,1/2)$ be a constant. There is a constant $\kappa>0$, depending only on $\delta$, such that every $(\delta,\tau)$-ball-subspace-evading function $f:\{0,1\}^d\to\mathbb R^s$ satisfies
--   $$s\ge\exp(\kappa\tau^2/d).$$
--
--   This is the main technical result of the paper, and it holds for any function with this property, without reference to streams or sketches.
--
--   **Formalization Note** The hypothesis fails when $\tau\ge d$, in particular when $d=0$, since then $\mathcal B(x,\tau)$ is the whole cube, so no restriction on $d$ and $\tau$ is needed.
--
--   Differences from the source:
--   - encoding: s = exp(Ω(τ²/d)) "for a constant δ ∈ (0,1/2)" → ∀ δ ∈ (0,1/2), ∃ κ > 0, ∀ d τ s f: exp(κτ²/d) ≤ s; reason: Ω is a lower bound, and its constant may depend on the constant δ but not on d, τ, s, f
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.8, Lemma 3.4; proof §3.1, pp.9–13

import Mathlib
import Definitions.Def_EuclidDiamStream_IsBallSubspaceEvading

namespace EuclidDiamStream

/-- Lemma 3.4 (Main Lemma) of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.8: if `f : {0,1}^d → ℝ^s` is `(δ,τ)`-ball-subspace-evading for a constant
`δ ∈ (0,1/2)`, then `s = exp(Ω(τ²/d))`.

**Formalization Note.** "`s = exp(Ω(·))`" is a lower bound, and `κ` may depend on the constant `δ` but not on
`d, τ, s, f`. The hypothesis fails when `τ ≥ d` (in particular `d = 0`), since then `B(x,τ)` is the whole cube, so
no restriction on `d, τ` is needed. -/
theorem lemma_3_4 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (d τ s : ℕ) (f : Cube d → (Fin s → ℝ)), IsBallSubspaceEvading δ τ f →
      Real.exp (κ * (τ : ℝ) ^ 2 / (d : ℝ)) ≤ (s : ℝ) := by sorry

end EuclidDiamStream
