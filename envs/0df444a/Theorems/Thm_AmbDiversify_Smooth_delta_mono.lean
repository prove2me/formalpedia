-- Prove2me | Theorems.Thm_AmbDiversify_Smooth_delta_mono
-- name    : AmbDiversify.Smooth.delta_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:06.970429+00:00
-- url     : https://prove2.me/theorems/eae9d525-9304-4e57-83bf-d499ee530e60
-- title:
--   Proof of Props 4.1–4.2, p. 16 (PDF 17) — p1 ≥ p2 ≥ 0.5 gives ∆(2) ≥ ∆(1), strictly for p1 > p2
-- statement:
--   Let $u:\mathbb R\to\mathbb R$, $W_0,L\in\mathbb R$, and let $\tfrac12\le p_2\le p_1\le 1$. Write $\Delta(\theta)=VD_{risk}(p_\theta)$.
--
--   1. If $u$ is concave, then $\Delta(1)\le\Delta(2)$.
--   2. If moreover $p_1>p_2$, $L>0$ and $u$ is strictly concave, then
--
--   $$\Delta(1)<\Delta(2).$$
--
--   The paper uses this as the sufficient condition "$p_1>p_2\ge 0.5$" for $\Delta(2)>\Delta(1)$ in case (ii) of Proposition 4.1: the expert who is more pessimistic about the ship also values diversification less.
--
--   **Formalization Note** Part 1, the weak form, is what the proof of the goal needs and holds for every concave $u$; part 2 is the page's strict form, which requires $L>0$ and strict concavity (with $L=0$ or a linear $u$ both values are $0$). The page's "without loss of generality $p_1>p_2$" is kept as the ordering hypothesis.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), p. 16 (PDF 17), proof of Propositions 4.1 and 4.2, '… a sufficient condition is p1 > p2 ≥ 0.5'

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

namespace AmbDiversify.Smooth

/-- Proof of Propositions 4.1 and 4.2, p. 16: for `1/2 ≤ p2 ≤ p1 ≤ 1`, `∆(2) ≥ ∆(1)` under a
concave utility, and `∆(2) > ∆(1)` when `p1 > p2`, `L > 0` and the utility is strictly concave. -/
theorem delta_mono (u : ℝ → ℝ) (W0 L p1 p2 : ℝ) (hp2 : 1 / 2 ≤ p2) (h21 : p2 ≤ p1) (hp1 : p1 ≤ 1) :
    (ConcaveOn ℝ Set.univ u → VD_risk u W0 L p1 ≤ VD_risk u W0 L p2) ∧
    (p2 < p1 → 0 < L → StrictConcaveOn ℝ Set.univ u →
      VD_risk u W0 L p1 < VD_risk u W0 L p2) := by sorry

end AmbDiversify.Smooth
