-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_thm_3_3_sequence_rate
-- name    : ConvexOptAlg.SmoothGD.thm_3_3_sequence_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:05:53.455982+00:00
-- url     : https://prove2.me/theorems/562bd576-8eb4-4e79-af1d-4195c0b278e2
-- title:
--   §3.2, proof of Theorem 3.3, p. 269 — ωδ_s² + δ_{s+1} ≤ δ_s for all s ≥ 1 implies 1/δ_t ≥ ω(t − 1)
-- statement:
--   Let $(\delta_s)_{s\ge1}$ be a sequence of non-negative reals and $\omega>0$, and suppose that for every $s\ge1$,
--   $$\omega\,\delta_s^2+\delta_{s+1}\le\delta_s.$$
--   Then for every $t\ge2$,
--
--   $$\omega\,(t-1)\,\delta_t\le 1,$$
--
--   i.e. $1/\delta_t\ge\omega(t-1)$ whenever $\delta_t>0$.
--
--   This is the purely numerical step of the proof of Theorem 3.3: applied with $\omega=1/(2\beta\|x_1-x^*\|^2)$ to the optimality gaps, it gives the rate $\delta_t\le 2\beta\|x_1-x^*\|^2/(t-1)$.
--
--   **Formalization Note** The page divides by $\delta_s$ and $\delta_{s+1}$; the Lean conclusion is multiplied through by $\delta_t$ so that it also covers $\delta_t=0$. The page defines $\omega=1/(2\beta\|x_1-x^*\|^2)>0$ in the nontrivial case; this lemma carries that positivity explicitly.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, proof of Theorem 3.3, first display on p. 269

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Proof of Theorem 3.3, first display on p. 269 (Bubeck, arXiv:1405.4980v2), as a lemma on real
sequences: if `ω > 0`, `δ_s ≥ 0` and `ω δ_s² + δ_{s+1} ≤ δ_s` for every `s ≥ 1`, then for every `t ≥ 2`,
`ω (t − 1) δ_t ≤ 1`, i.e. `1/δ_t ≥ ω(t − 1)` whenever `δ_t > 0`. Stated without division so
that it also covers `δ_t = 0`. -/
theorem thm_3_3_sequence_rate (δ : ℕ → ℝ) (ω : ℝ) (hω : 0 < ω)
    (hδ : ∀ s : ℕ, 1 ≤ s → 0 ≤ δ s)
    (hrec : ∀ s : ℕ, 1 ≤ s → ω * δ s ^ 2 + δ (s + 1) ≤ δ s) (t : ℕ) (ht : 2 ≤ t) :
    ω * ((t : ℝ) - 1) * δ t ≤ 1 := by sorry

end ConvexOptAlg.SmoothGD
