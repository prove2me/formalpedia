-- Prove2me | Theorems.Thm_CompOT_W1_prop_6_1_lipschitz_of_cTransform
-- name    : CompOT.W1.prop_6_1_lipschitz_of_cTransform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:44.783247+00:00
-- url     : https://prove2.me/theorems/34c0ac3f-d1b6-4e50-ae53-4704fb976354
-- title:
--   Proof of Proposition 6.1, p. 472 — for c = d, every real-valued c-transform g^c is 1-Lipschitz
-- statement:
--   Let $(\mathcal X,d)$ be a metric space with cost $c(x,y)=d(x,y)$, let $g:\mathcal X\to\mathbb R$ be any function and suppose that its $c$-transform $g^c(y)=\inf_{x}\,d(x,y)-g(x)$ is real valued and equal to $f:\mathcal X\to\mathbb R$. Then $f$ is 1-Lipschitz:
--
--   $$
--   |f(x)-f(y)|\le d(x,y)\qquad\text{for all }x,y\in\mathcal X,
--   $$
--
--   that is, $\mathrm{Lip}(f)\le 1$.
--
--   This is the "only if" half of Proposition 6.1: $c$-concave functions for a metric cost are 1-Lipschitz.
--
--   **Formalization Note** $\mathrm{Lip}(f)\le1$ is Mathlib's `LipschitzWith 1 f`, which is equivalent to the book's $\sup_{x\ne y}|f(x)-f(y)|/d(x,y)\le1$. The equality $f=g^c$ is an equality in `EReal`, so it includes the finiteness of $g^c$. The function $g$ is not required to be continuous (the book's $g\in\mathcal C(\mathcal X)$); the statement is therefore slightly more general.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §6.1, proof of Proposition 6.1, first paragraph, p. 472

import Mathlib
import Definitions.Def_CompOT_W1_Defs

namespace CompOT.W1

/-- Proof of Proposition 6.1, p. 472 (first paragraph): if `f = g^c` for the cost `c = d`,
then `Lip(f) ≤ 1`. Here `g` is any real function on `X` and `f` is real valued. -/
theorem prop_6_1_lipschitz_of_cTransform {X : Type*} [MetricSpace X] (f g : X → ℝ)
    (hfg : ∀ y, (f y : EReal) = cTransform g y) :
    LipschitzWith 1 f := by sorry

end CompOT.W1
