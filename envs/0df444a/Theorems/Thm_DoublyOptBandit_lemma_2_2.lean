-- Prove2me | Theorems.Thm_DoublyOptBandit_lemma_2_2
-- name    : DoublyOptBandit.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:26:58.308447+00:00
-- url     : https://prove2.me/theorems/e96102f6-fb84-4dfe-8a2e-6fa1ec85af38
-- title:
--   Lemma 2.2 — the Dikin ellipsoid lies in $X$, and Hessians are comparable on it (corrected: $(1-r)^2$ lower bound, $r<1$)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex and let $R$ be a $\nu$-self-concordant barrier for $X$. Let $x\in\operatorname{int}X$ and write $\|h\|_x=\sqrt{h^\top\nabla^2R(x)h}$.
--
--   1. The Dikin ellipsoid $W(x)=\{x':\|x'-x\|_x\le1\}$ is contained in $X$.
--   2. For every $x'$ with $r=\|x'-x\|_x<1$ and every $h\in\mathbb R^n$,
--   $$
--   (1-r)^2\,h^\top\nabla^2R(x)h\ \le\ h^\top\nabla^2R(x')h\ \le\ (1-r)^{-2}\,h^\top\nabla^2R(x)h .
--   $$
--
--   Part 1 guarantees that the played points $x+Az$ of the algorithms are feasible, so the bandit feedback is a value of the reward on $X$.
--
--   Differences from the source:
--   - correction: (1 − ‖x′ − x‖ₓ)∇²R(x) ⪯ ∇²R(x′) ⪯ (1 − ‖x′ − x‖ₓ)⁻²∇²R(x) for all x′ ∈ W(x) → (1 − r)²∇²R(x) ⪯ ∇²R(x′) ⪯ (1 − r)⁻²∇²R(x) for r = ‖x′ − x‖ₓ < 1; reason: false as printed: X = [0, 2], R(x) = −log x − log(2 − x), x = 0.2, x′ = 0.2 + 0.5/√∇²R(0.2) gives r = 0.5 and ∇²R(x′) ≈ 11.502 < 12.654 ≈ (1 − r)∇²R(x); the cited NN94 Theorem 2.1.1 has (1 − r)², and (1 − r)⁻² is undefined at r = 1
--   - generalization: X closed, convex and compact (standing assumption of §2) → X closed and convex; reason: Definition 2.1 and the cited theorem need only a closed convex X; compact X are instances
--   - encoding: Loewner order ⪯ between Hessians → inequalities between the quadratic forms h⊤∇²R(·)h for every h, Hessian as iteratedFDeriv ℝ 2; reason: definition of ⪯; same instances
--   - encoding: R : int(X) → ℝ a ν-self-concordant barrier (Definition 2.1) → a total function satisfying the published IsNuSelfConcordantBarrier, whose convexity clause Definition 2.1 presupposes; reason: the powers (h⊤∇²R(x)h)^{1/2}, ^{3/2} of Definition 2.1 require ∇²R ⪰ 0 on the convex open set int X, i.e. convexity
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Lemma 2.2, p.6 (citing Nesterov and Nemirovski 1994, Theorem 2.1.1); Dikin ellipsoid, p.6; Definition 2.1, p.5

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_DoublyOptBandit_LocalNorm

namespace DoublyOptBandit

/-- **Lemma 2.2** (Ba, Lin, Zhang & Zhou, arXiv:2112.02856v4, Lemma 2.2, p.6; citing Nesterov and
Nemirovski 1994, Theorem 2.1.1), corrected in part 2. Let `X ⊆ ℝⁿ` be closed and convex, `R` a
`ν`-self-concordant barrier for `X` (Definition 2.1, p.5) and `x ∈ int X`. Then
1. the Dikin ellipsoid `W(x) = {x′ : ‖x′ − x‖ₓ ≤ 1}` is contained in `X`;
2. for every `x′` with `r = ‖x′ − x‖ₓ < 1` and every `h`,
   `(1 − r)² h⊤∇²R(x)h ≤ h⊤∇²R(x′)h ≤ (1 − r)⁻² h⊤∇²R(x)h`.

**Formalization Note** The printed part 2 reads `(1 − ‖x′ − x‖ₓ)∇²R(x) ⪯ ∇²R(x′)` for all
`x′ ∈ W(x)`. It is false: for `X = [0, 2]`, `R(x) = −log x − log(2 − x)`, `x = 0.2` and
`x′ = 0.2 + 0.5/√(∇²R(0.2))` (so `r = 0.5`), `∇²R(x′) ≈ 11.502 < 12.654 ≈ (1 − r)∇²R(x)`. The cited
source has `(1 − r)²`; at `r = 1` the factor `(1 − r)⁻²` is undefined, so part 2 is stated for
`r < 1`. The Loewner inequalities are stated as inequalities of quadratic forms for every `h`. -/
theorem lemma_2_2 {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) (hXcl : IsClosed X)
    (hXcv : Convex ℝ X) (R : EuclideanSpace ℝ (Fin m) → ℝ) (ν : ℝ)
    (hR : EntropicBarrier.Universal.IsNuSelfConcordantBarrier X R ν)
    (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ interior X) :
    dikinEllipsoid R x ⊆ X ∧
      ∀ x' : EuclideanSpace ℝ (Fin m), localNorm R x (x' - x) < 1 →
        ∀ h : EuclideanSpace ℝ (Fin m),
          (1 - localNorm R x (x' - x)) ^ 2 * hessForm R x h ≤ hessForm R x' h ∧
            hessForm R x' h ≤ ((1 - localNorm R x (x' - x)) ^ 2)⁻¹ * hessForm R x h := by sorry

end DoublyOptBandit
