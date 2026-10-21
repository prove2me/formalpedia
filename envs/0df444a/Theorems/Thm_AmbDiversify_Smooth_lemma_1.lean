-- Prove2me | Theorems.Thm_AmbDiversify_Smooth_lemma_1
-- name    : AmbDiversify.Smooth.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:10.260833+00:00
-- url     : https://prove2.me/theorems/9abd7631-f928-4441-a4c8-18c0703ef4e4
-- title:
--   Lemma 1, p. 16 (PDF 17) — DAAA/CAAA/IAAA ⇒ φ⁻¹(E φ(x̃ + z)) >/=/< φ⁻¹(E φ(x̃)) + z, two-point x̃
-- statement:
--   Let $\phi:\mathbb R\to\mathbb R$ be twice continuously differentiable with $\phi'>0$ everywhere, and let $\lambda=-\phi''/\phi'$. Let $\tilde x$ be the two-point random variable taking the value $x_1$ with probability $\mu$ and $x_2\neq x_1$ with probability $1-\mu$, where $0<\mu<1$, and let $z>0$. Write $CE_\phi(\mu;a,b)=\phi^{-1}(\mu\phi(a)+(1-\mu)\phi(b))$. Then:
--
--   1. if $\lambda$ is strictly decreasing (DAAA), $CE_\phi(\mu;x_1+z,x_2+z) > CE_\phi(\mu;x_1,x_2)+z$;
--   2. if $\lambda$ is constant (CAAA), $CE_\phi(\mu;x_1+z,x_2+z) = CE_\phi(\mu;x_1,x_2)+z$;
--   3. if $\lambda$ is strictly increasing (IAAA), $CE_\phi(\mu;x_1+z,x_2+z) < CE_\phi(\mu;x_1,x_2)+z$.
--
--   In expectation notation, $\phi^{-1}(\mathbb E[\phi(\tilde x+z)]) \;>\;(=,\,<)\; \phi^{-1}(\mathbb E[\phi(\tilde x)])+z$. This is Pratt's characterization of decreasing, constant and increasing absolute aversion through certainty equivalents, applied to the ambiguity function: it says how the certainty equivalent of the expert-wise utilities reacts when every expert's utility rises by the same amount.
--
--   **Formalization Note** The paper states Lemma 1 for a utility $u$ and an arbitrary random variable, as an equivalence; its proof of Propositions 4.1 and 4.2 applies it "with the ambiguity function $\phi$" on the two-expert distribution. Only that use is formalized: the "$\Rightarrow$" direction, for two-point $\tilde x$. The strict cases need a nondegenerate $\tilde x$ ($x_1\ne x_2$, $0<\mu<1$), since for a degenerate one equality holds; these hypotheses are **added**. No concavity of $\phi$ is assumed. $\phi^{-1}$ is `Function.invFun φ`.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), p. 16 (PDF 17), Lemma 1, (A.5), proof of Propositions 4.1 and 4.2

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

namespace AmbDiversify.Smooth

/-- Lemma 1, p. 16, applied to the ambiguity function `φ` (as the proof of Propositions 4.1 and
4.2 does), "⇒" direction, for the two-point random variable `x̃ = (x1, µ; x2, 1 − µ)` and `z > 0`:
DAAA gives `φ⁻¹(E φ(x̃ + z)) > φ⁻¹(E φ(x̃)) + z`, CAAA gives equality, IAAA gives `<`.
The strict cases need a nondegenerate `x̃` (`x1 ≠ x2`, `0 < µ < 1`). -/
theorem lemma_1 (φ : ℝ → ℝ) (hφ2 : ContDiff ℝ 2 φ) (hφ1 : ∀ x, 0 < deriv φ x)
    (μ x1 x2 z : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hx : x1 ≠ x2) (hz : 0 < z) :
    (DAAA φ → smoothCE φ μ x1 x2 + z < smoothCE φ μ (x1 + z) (x2 + z)) ∧
    (CAAA φ → smoothCE φ μ (x1 + z) (x2 + z) = smoothCE φ μ x1 x2 + z) ∧
    (IAAA φ → smoothCE φ μ (x1 + z) (x2 + z) < smoothCE φ μ x1 x2 + z) := by sorry

end AmbDiversify.Smooth
