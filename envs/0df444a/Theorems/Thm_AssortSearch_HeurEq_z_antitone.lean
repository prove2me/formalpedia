-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_z_antitone
-- name    : AssortSearch.HeurEq.z_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:19.133596+00:00
-- url     : https://prove2.me/theorems/b0d3a523-af1e-4677-bf49-9ca318b5fe83
-- title:
--   $Z(\delta)=\delta e^{-\lambda\delta}/(1-e^{-\lambda\delta})$ is decreasing on $(0,\infty)$
-- statement:
--   Let $\lambda>0$ and define, for $\delta>0$,
--   $$Z(\delta)=\frac{\delta\exp(-\lambda\delta)}{1-\exp(-\lambda\delta)}.$$
--   Then $Z$ is a decreasing (non-increasing) function of $\delta$ on $(0,\infty)$.
--
--   In the proof of Theorem 7 the no-purchase bias of the estimates reduces to comparing $Z$ at the total preferences $\sum_{j=0}^{x'}v_j$ and $\sum_{j=0}^{x}v_j$ of two assortments; monotonicity of $Z$ settles the comparison.
--
--   **Formalization Note** "Decreasing" is formalized as `AntitoneOn` on $(0,\infty)$, the property the paper's argument ($Z'\le 0$) establishes; the denominator vanishes at $\delta=0$, which is excluded.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 23 (PDF 25), proof of Theorem 7, definition of Z(δ) and its monotonicity

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

/-- Proof of Theorem 7, p. 23: for `λ > 0`, the function
`Z(δ) = δ exp(−λδ) / (1 − exp(−λδ))` is decreasing in `δ` on `(0, ∞)`. -/
theorem z_antitone (lam : ℝ) (hlam : 0 < lam) :
    AntitoneOn
      (fun δ : ℝ => δ * Real.exp (-(lam * δ)) / (1 - Real.exp (-(lam * δ))))
      (Set.Ioi 0) := by sorry

end AssortSearch.HeurEq
