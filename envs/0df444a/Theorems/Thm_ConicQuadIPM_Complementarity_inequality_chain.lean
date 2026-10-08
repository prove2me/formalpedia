-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_inequality_chain
-- name    : ConicQuadIPM.Complementarity.inequality_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:25.238307+00:00
-- url     : https://prove2.me/theorems/cc3dca0a-07e7-469e-8017-af323cc8878e
-- title:
--   Appendix, p. 36 — xᵀs = Σ(Tⁱxⁱ)ᵀTⁱsⁱ ≥ Σ((Tⁱxⁱ)₁(Tⁱsⁱ)₁ − ‖·‖‖·‖) ≥ Σ√((xⁱ)ᵀQⁱxⁱ(sⁱ)ᵀQⁱsⁱ) ≥ 0
-- statement:
--   Let $K=K^1\times\dots\times K^k$ be as in §3 and $x,s\in K$. Then
--   $$
--   \begin{aligned}
--   x^Ts&=\sum_{i=1}^k (T^ix^i)^TT^is^i\\
--   &\ge \sum_{i=1}^k \Bigl((T^ix^i)_1(T^is^i)_1-\|(T^ix^i)_{2:n}\|\,\|(T^is^i)_{2:n}\|\Bigr)\\
--   &\ge \sum_{i=1}^k \sqrt{(x^i)^TQ^ix^i\,(s^i)^TQ^is^i}\\
--   &\ge 0 .
--   \end{aligned}
--   $$
--   The first inequality is the Cauchy–Schwarz inequality, the second uses $T^ix^i,T^is^i\in K^q$.
--
--   The chain shows that $x^Ts=0$ forces every term to vanish, which drives the converse direction of Lemma 3.1; it also bounds each $\sqrt{\cdot}$ term of the neighbourhood $\mathcal N(\beta)$.
--
--   **Formalization Note.** The page writes the chain under the assumption $x^Ts=0$ (starting with $0=x^Ts$); the inequalities themselves hold for all $x,s\in K$ and are stated so. $\|\cdot\|$ is the Euclidean norm, written as $\sqrt{\texttt{tailSq}\,\cdot\,1}$. Block dimensions (`WellFormed`) are a disclosed hypothesis.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, Appendix, proof of Lemma 3.1, pp. 36–37 (the displayed chain and the sentence following it)

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem inequality_chain {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ)
    (hx : inK kind x) (hs : inK kind s) :
    ∑ i, x i ⬝ᵥ s i = ∑ i, (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) ∧
    ∑ i, (coord (Tmat (kind i) (n i) *ᵥ x i) 0 * coord (Tmat (kind i) (n i) *ᵥ s i) 0 -
        Real.sqrt (tailSq (Tmat (kind i) (n i) *ᵥ x i) 1) *
          Real.sqrt (tailSq (Tmat (kind i) (n i) *ᵥ s i) 1))
      ≤ ∑ i, (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) ∧
    ∑ i, Real.sqrt ((x i ⬝ᵥ (Qmat (kind i) (n i) *ᵥ x i)) *
        (s i ⬝ᵥ (Qmat (kind i) (n i) *ᵥ s i)))
      ≤ ∑ i, (coord (Tmat (kind i) (n i) *ᵥ x i) 0 * coord (Tmat (kind i) (n i) *ᵥ s i) 0 -
        Real.sqrt (tailSq (Tmat (kind i) (n i) *ᵥ x i) 1) *
          Real.sqrt (tailSq (Tmat (kind i) (n i) *ᵥ s i) 1)) ∧
    0 ≤ ∑ i, Real.sqrt ((x i ⬝ᵥ (Qmat (kind i) (n i) *ᵥ x i)) *
        (s i ⬝ᵥ (Qmat (kind i) (n i) *ᵥ s i))) := by sorry

end ConicQuadIPM.Complementarity
