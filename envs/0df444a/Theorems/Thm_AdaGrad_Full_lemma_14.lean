-- Prove2me | Theorems.Thm_AdaGrad_Full_lemma_14
-- name    : AdaGrad.Full.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:45:18.362959+00:00
-- url     : https://prove2.me/theorems/1c96b61e-9aa6-4900-84a2-6a172808bf40
-- title:
--   Lemma 14 — $\nabla_X\operatorname{tr}(X^p)=pX^{p-1}$ for $X\succ0$
-- statement:
--   Let $p\in\mathbb R$ and let $X$ be a real symmetric positive definite $d\times d$ matrix. Then the gradient of $X\mapsto\operatorname{tr}(X^p)$ on symmetric matrices is $pX^{p-1}$: for every symmetric direction $A$,
--   $$\frac{d}{ds}\Big|_{s=0}\operatorname{tr}\big((X+sA)^p\big)=p\operatorname{tr}\big(X^{p-1}A\big).$$
--
--   The paper uses it with $p=\tfrac12$ to obtain the gradient $\tfrac12A^{-1/2}$ of $\operatorname{tr}(A^{1/2})$ in the proof of Lemma 8.
--
--   **Formalization Note** The gradient with respect to the trace inner product on symmetric matrices is stated as a derivative (`HasDerivAt`) of $s\mapsto\operatorname{tr}((X+sA)^p)$ at $s=0$ along every symmetric $A$. The powers $X^p$ are the functional calculus of $x\mapsto x^p$ (real power), which is the usual matrix power on the positive definite matrices near $X$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2149, Lemma 14

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

namespace AdaGrad.Full

/-- Lemma 14 (p. 2149): for `p ∈ ℝ` and `X ≻ 0`, `∇_X tr(X^p) = p X^{p−1}`, stated as the
directional derivative of `s ↦ tr((X + sA)^p)` at `s = 0` along every symmetric direction `A`. -/
theorem lemma_14 {d : ℕ} (p : ℝ) (X A : Matrix (Fin d) (Fin d) ℝ) (hX : X.PosDef)
    (hA : A.IsHermitian) :
    HasDerivAt (fun s : ℝ => (cfc (fun x : ℝ => x ^ p) (X + s • A)).trace)
      (p * (cfc (fun x : ℝ => x ^ (p - 1)) X * A).trace) 0 := by sorry

end AdaGrad.Full
