-- Prove2me | Theorems.Thm_AmbDiversify_Smooth_proposition_1
-- name    : AmbDiversify.Smooth.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:08.807098+00:00
-- url     : https://prove2.me/theorems/1cb289a0-dc06-4114-bcd9-3a53894845d2
-- title:
--   Proposition 1, p. 4 (PDF 5) — VD ≥ 0 for all W0, L > 0, p ∈ [0, 1] iff u is concave
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be a continuous utility function. The value of diversification is nonnegative in every instance of the shipping problem if and only if the decision maker is risk averse:
--
--   $$\Big(\forall\, W_0\in\mathbb R,\ L>0,\ p\in[0,1]:\ VD_{risk}(W_0,L,p)\ge 0\Big)\iff u \text{ is concave on } \mathbb R.$$
--
--   This is the paper's version of Bernoulli's diversification principle: splitting the cargo over two ships is (weakly) preferred by exactly the risk-averse expected-utility maximizers.
--
--   **Formalization Note** The page writes "$VD\ge 0 \iff u$ is concave"; "positive" is the displayed $\ge 0$. The left side is quantified over all sure wealths $W_0$, losses $L>0$ and probabilities $p\in[0,1]$, the only reading under which "$\Rightarrow$" holds (a single instance gives a single midpoint inequality). Continuity of $u$ is **added**: without it, a midpoint-concave but non-concave (Hamel-type) $u$ makes "$\Rightarrow$" false.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), p. 4 (PDF 5), Proposition 1; proof p. 15 (PDF 16)

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

namespace AmbDiversify.Smooth

/-- Proposition 1, p. 4: for a continuous utility `u`, the value of diversification is
nonnegative for every sure wealth `W0`, every loss `L > 0` and every probability `p ∈ [0, 1]`
if and only if `u` is concave. -/
theorem proposition_1 (u : ℝ → ℝ) (hu_cont : Continuous u) :
    (∀ W0 L p : ℝ, 0 < L → 0 ≤ p → p ≤ 1 → 0 ≤ VD_risk u W0 L p) ↔
      ConcaveOn ℝ Set.univ u := by sorry

end AmbDiversify.Smooth
