-- Prove2me | Theorems.Thm_AffinePSD_InfDiv_theorem_2_9
-- name    : AffinePSD.InfDiv.theorem_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:17.077195+00:00
-- url     : https://prove2.me/theorems/88b9ad92-d961-4ac3-b37b-2be97a521f7c
-- title:
--   Theorem 2.9 — for $d\ge2$: infinitely decomposable $\iff$ affine with $\alpha=0$ $\iff$ affine and infinitely divisible
-- statement:
--   Let $d\ge2$ and let $(P_x)_{x\in S_d^+}\in\mathcal P$, the law of a stochastically continuous Markov process $X$ on $S_d^+$ (possibly killed) started at $x$, with transition family $p$. The following assertions are equivalent:
--
--   1. $(P_x)_{x\in S_d^+}$ is infinitely decomposable: for every $k\ge1$ there is $(P^{(k)}_x)\in\mathcal P$ with
--   $$P_{x^{(1)}+\dots+x^{(k)}}=P^{(k)}_{x^{(1)}}*\dots*P^{(k)}_{x^{(k)}}\qquad\forall x^{(1)},\dots,x^{(k)}\in S_d^+;$$
--   2. $(X,(P_x))$ is affine with vanishing diffusion parameter $\alpha=0$;
--   3. $(X,(P_x))$ is affine and infinitely divisible: every marginal $P_x\circ X_t^{-1}$ is infinitely divisible.
--
--   On $\mathbb R_+^m\times\mathbb R^n$, regular affine processes and infinitely decomposable Markov processes are the same class. On $S_d^+$ with $d\ge2$ they are not: the infinitely decomposable ones are exactly the affine processes without diffusion part. For instance, the Wishart processes of Bru are affine but not infinitely divisible. The hypothesis $d\ge2$ is essential. The $k$-th root of an infinitely decomposable affine process has drift $b/k$, and the admissibility condition $b/k\succeq(d-1)\alpha$ for all $k$ (Proposition 4.18) forces $\alpha=0$ only when $d\ge2$. For $d=1$, the Cox–Ingersoll–Ross process has $\alpha\ne0$ and is infinitely decomposable.
--
--   **Formalization Note** The transition family $p$ of $(P_x)$ is named (`InPWith`); it is unique for $t\ge0$. Affinity and infinite divisibility of the marginals are properties of $p$. Paths, $\mathcal P$ and $*$ are encoded as in the `PathSpace` definitions: all paths with the product σ-algebra, with $\Delta$ absorbing in law and for addition. The infinite divisibility of a marginal is that of its restriction $p_t(x,\cdot)$ to $S_d^+$, as a sub-probability measure. "Affine with $\alpha=0$" refers to the admissible parameter set of Theorem 2.4, which is unique. $\chi$ is any truncation function; $\alpha$ does not depend on it.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §2, Theorem 2.9, p. 12; proof §6.3, pp. 55–56

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone
import Definitions.Def_AffinePSD_Necessity_Params
import Definitions.Def_AffinePSD_Necessity_Process
import Definitions.Def_AffinePSD_InfDiv_PathSpace
import Definitions.Def_AffinePSD_InfDiv_InfDivisible

open MeasureTheory ProbabilityTheory

namespace AffinePSD.InfDiv

/-- Theorem 2.9 (arXiv:0910.0137v3, §2, p. 12). Let `d ≥ 2` and `(P_x)_{x ∈ S_d^+} ∈ 𝒫`. The
following are equivalent:
(i) `(P_x)` is infinitely decomposable;
(ii) `(X, (P_x))` is affine with vanishing diffusion parameter `α = 0`;
(iii) `(X, (P_x))` is affine and infinitely divisible.
Formalization Note: `p` is the transition family of `(P_x)` (`InPWith`), unique for `t ≥ 0`;
affinity and the marginals are properties of `p`. Paths, `𝒫` and `∗` are encoded as in `Path`,
`InPWith`, `convK` (all paths with the product σ-algebra, `Δ` absorbing in law and for addition).
`χ` is any truncation function; `α` does not depend on it. -/
theorem theorem_2_9 {d : ℕ} (hd : 2 ≤ d) (χ : AffinePSD.Necessity.Trunc d) (Px : AffinePSD.Necessity.Cone d → Measure (Path d))
    (p : ℝ → Kernel (AffinePSD.Necessity.Cone d) (AffinePSD.Necessity.Cone d)) (hP : InPWith Px p) :
    (InfDecomp Px ↔ AffineZeroDiff χ p) ∧
      (AffineZeroDiff χ p ↔
        ((∃ (φ : ℝ → AffinePSD.Necessity.Mat d → ℝ) (ψ : ℝ → AffinePSD.Necessity.Mat d → AffinePSD.Necessity.Mat d), AffinePSD.Necessity.IsAffineWith p φ ψ) ∧
          InfDivMarginals p)) := by sorry

end AffinePSD.InfDiv
