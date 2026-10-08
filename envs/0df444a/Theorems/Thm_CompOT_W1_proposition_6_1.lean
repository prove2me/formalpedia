-- Prove2me | Theorems.Thm_CompOT_W1_proposition_6_1
-- name    : CompOT.W1.proposition_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:53.971372+00:00
-- url     : https://prove2.me/theorems/0a63223e-bd41-413f-b42c-fc7cd3ad667a
-- title:
--   Proposition 6.1, p. 472 — for c = d, f = g^c for some g if and only if Lip(f) ≤ 1, and then f^c = −f
-- statement:
--   Let $d$ be a distance on $\mathcal X=\mathcal Y$ and use the ground cost $c(x,y)=d(x,y)$. For a function $g$ on $\mathcal X$ write $g^c(y)=\inf_{x\in\mathcal X} d(x,y)-g(x)$ for its $c$-transform, and for $f$ write
--
--   $$
--   \mathrm{Lip}(f)=\sup\left\{\frac{|f(x)-f(y)|}{d(x,y)} : (x,y)\in\mathcal X^2,\ x\ne y\right\}.
--   $$
--
--   Then, for every real function $f$ on $\mathcal X$:
--
--   1. there exists a continuous $g:\mathcal X\to\mathbb R$ with $f=g^c$ if and only if $\mathrm{Lip}(f)\le1$;
--   2. if $\mathrm{Lip}(f)\le 1$, then $f^c=-f$.
--
--   The proposition characterizes the $c$-concave functions for a metric cost as exactly the 1-Lipschitz ones, and shows that their $c$-transform is simply $-f$. It is what reduces the Kantorovich dual problem for $\mathcal W_1$ to a single 1-Lipschitz potential, i.e. to the Kantorovich–Rubinstein formula (6.1).
--
--   **Formalization Note** $\mathcal X$ is any Lean `MetricSpace`; $\mathrm{Lip}(f)\le1$ is `LipschitzWith 1 f`, equivalent to the supremum above. The infimum defining $g^c$ is taken in `EReal`, and "$f=g^c$" is an equality in `EReal`, so it includes that $g^c$ is finite everywhere. The book's $g\in\mathcal C(\mathcal Y)$ is kept as `Continuous g`; the book's $f\in\mathcal C(\mathcal X)$ is not assumed, since each side of the equivalence already forces $f$ to be 1-Lipschitz, hence continuous.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 6.1, p. 472 (proof pp. 472–473)

import Mathlib
import Definitions.Def_CompOT_W1_Defs

namespace CompOT.W1

/-- Proposition 6.1, p. 472. Let `d` be a distance on `X = Y` and `c(x, y) = d(x, y)`. Then a
real function `f` on `X` is of the form `f = g^c` for some continuous `g` if and only if
`Lip(f) ≤ 1`; furthermore, if `Lip(f) ≤ 1`, then `f^c = -f`. -/
theorem proposition_6_1 {X : Type*} [MetricSpace X] (f : X → ℝ) :
    ((∃ g : X → ℝ, Continuous g ∧ ∀ y, (f y : EReal) = cTransform g y) ↔
        LipschitzWith 1 f) ∧
      (LipschitzWith 1 f → ∀ y, cTransform f y = ((-f y : ℝ) : EReal)) := by sorry

end CompOT.W1
