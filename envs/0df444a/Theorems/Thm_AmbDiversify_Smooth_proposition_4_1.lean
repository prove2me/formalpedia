-- Prove2me | Theorems.Thm_AmbDiversify_Smooth_proposition_4_1
-- name    : AmbDiversify.Smooth.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:07.862119+00:00
-- url     : https://prove2.me/theorems/a528aa9e-d9fa-4906-b3d9-75581ca50972
-- title:
--   Proposition 4.1, p. 10 (PDF 11) — under IAAA with p1 = 1 − p2, or CAAA/IAAA with pθ ≥ 0.5, VD_smt ≤ VD_AN
-- statement:
--   Consider the shipping problem with sure wealth $W_0$, cargo value $L>0$, two experts with perishing probabilities $p_1,p_2\in[0,1]$ and prior weights $\mu,1-\mu$ with $\mu\in[0,1]$. Let the utility $u:\mathbb R\to\mathbb R$ be nondecreasing and concave (a risk-averse decision maker), and let $\phi$ be the ambiguity function of an ambiguity-averse decision maker ($C^2$, $\phi'>0$, concave) with coefficient of absolute ambiguity aversion $\lambda=-\phi''/\phi'$. Suppose that one of the following holds:
--
--   1. $\lambda$ is strictly increasing (IAAA) and $p_1 = 1-p_2$; or
--   2. $\lambda$ is constant (CAAA) or strictly increasing (IAAA), and $p_1\ge\tfrac12$, $p_2\ge\tfrac12$.
--
--   Then ambiguity aversion does not raise the value of diversification above its ambiguity-neutral level:
--
--   $$VD_{smt} \;=\; EU^D_{smt}-EU^{ND}_{smt}\;\le\; EU^D_{AN}-EU^{ND}_{AN} \;=\; VD_{AN}.$$
--
--   The result runs against the intuition that ambiguity aversion adds a motive to diversify: in the smooth ambiguity model of Klibanoff, Marinacci and Mukerji, under constant or increasing absolute ambiguity aversion and the stated conditions on the experts, the aggregation across experts can only shrink the gain from splitting the cargo.
--
--   **Formalization Note** "Decreases the value of diversification" is read, as in the proof's criterion (A.4), as the comparison $VD_{smt}\le VD_{AN}$ with the ambiguity-neutral benchmark (linear $\phi$, footnote 5). The inequality is weak: at $p_1=p_2$, at $\mu\in\{0,1\}$, or when $2u(W_0-L/2)=u(W_0-L)+u(W_0)$ the two values coincide, so a strict version is false. Added standing hypotheses: $u$ nondecreasing and concave (the paper's "under risk aversion (Proposition 1)", p. 10, and the ordering of the experts' utilities in case (ii)); $\phi$ of class $C^2$ with $\phi'>0$; $L>0$. IAAA/CAAA are monotonicity of $\lambda$. $\phi^{-1}$ is `Function.invFun φ`.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), p. 10 (PDF 11), Proposition 4.1; proof pp. 15–16 (PDF 16–17), (A.4)

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

namespace AmbDiversify.Smooth

/-- Proposition 4.1, p. 10: under the smooth ambiguity model with a risk-averse (nondecreasing,
concave) utility `u` and an ambiguity-averse `φ`, the value of diversification is at most its
ambiguity-neutral level, `VD_smt ≤ VD_AN`, if (i) IAAA and `p1 = 1 − p2`, or (ii) CAAA or IAAA and
`pθ ≥ 0.5` for both experts. -/
theorem proposition_4_1 (u φ : ℝ → ℝ) (W0 L μ p1 p2 : ℝ)
    (hL : 0 < L) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hp1_0 : 0 ≤ p1) (hp1_1 : p1 ≤ 1) (hp2_0 : 0 ≤ p2) (hp2_1 : p2 ≤ 1)
    (hu_mono : Monotone u) (hu_conc : ConcaveOn ℝ Set.univ u)
    (hφ : IsAmbiguityFunction φ)
    (hcase : (IAAA φ ∧ p1 = 1 - p2) ∨ ((CAAA φ ∨ IAAA φ) ∧ 1 / 2 ≤ p1 ∧ 1 / 2 ≤ p2)) :
    VD_smt φ u W0 L μ p1 p2 ≤ VD_AN u W0 L μ p1 p2 := by sorry

end AmbDiversify.Smooth
