-- Prove2me | Theorems.Thm_ExtrapBias_Beliefs_lemma_4
-- name    : ExtrapBias.Beliefs.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:07.03483+00:00
-- url     : https://prove2.me/theorems/97c43492-462a-4c16-90f5-9487aa1c6078
-- title:
--   Lemma 4, p. 40, corrected — filled ellipse and angle boundary give the same HJB
-- statement:
--   Fix the model parameters and numerical values F₀, F₁, F₂ and m. Form the scaled HJB bracket (25) from these values. Replace its angle parametrization by a distortion h in the filled ellipse H, with the permanent and temporary drift changes σδhᴾ and σYhᵀ. Then the attained max-min equations agree:
--   $$
--   rF_0=\max_i\min_{\phi\in[0,2\pi]} B_{25}(F_0,F_1,F_2,m,i,\phi)
--   \quad\Longleftrightarrow\quad
--   rF_0=\max_i\min_{h\in H} B_H(F_0,F_1,F_2,m,i,h).
--   $$
--   Thus the local HJB can minimize over the ellipse or its angular boundary without changing its value.
--
--   **Formalization Note** The working paper’s Lemma 4 omits σδ and σY in its h-form drift terms and shows a general γ in H. The theorem uses the factors from (11)–(12) and the γ=2 restriction of §2.3. Both extrema are encoded through explicit witnesses and bounds.
-- source:
--   Lee & Rivera, Extrapolation Bias and Dynamic Liquidity Management, working paper (May 24, 2019), p. 40, Lemma 4; pp. 9–11, (8), (11)–(13); p. 17, (25)

import Mathlib
import Definitions.Def_ExtrapBias_Beliefs_Model

namespace ExtrapBias.Beliefs

/-- Lemma 4, p. 40, corrected using σδ and σY in the h-drifts and γ = 2. -/
theorem lemma_4 (p : Params) (F0 F1 F2 m : ℝ) :
    ((∃ i : ℝ, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        p.r * F0 ≤ bracket25 p F0 F1 F2 m i φ) ∧
      (∀ i : ℝ, ∃ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        bracket25 p F0 F1 F2 m i φ ≤ p.r * F0)) ↔
    ((∃ i : ℝ, ∀ h ∈ ellipseH p,
        p.r * F0 ≤ bracketH p F0 F1 F2 m i h) ∧
      (∀ i : ℝ, ∃ h ∈ ellipseH p,
        bracketH p F0 F1 F2 m i h ≤ p.r * F0)) := by sorry

end ExtrapBias.Beliefs
