-- Prove2me | Theorems.Thm_CompOT_W1_prop_6_1_cTransform_self
-- name    : CompOT.W1.prop_6_1_cTransform_self
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:48.879181+00:00
-- url     : https://prove2.me/theorems/aa393218-1677-48cd-9904-60433df05aa5
-- title:
--   Proof of Proposition 6.1, p. 473 — if Lip(f) ≤ 1 then f^c = −f
-- statement:
--   Let $(\mathcal X,d)$ be a metric space with cost $c(x,y)=d(x,y)$ and let $f:\mathcal X\to\mathbb R$ satisfy $\mathrm{Lip}(f)\le1$. Then for every $y\in\mathcal X$,
--
--   $$
--   f^c(y)=\inf_{x\in\mathcal X}\,\bigl[d(x,y)-f(x)\bigr]=-f(y).
--   $$
--
--   This is the second claim of Proposition 6.1. It shows that for a metric cost the pair $(f,f^c)$ of dual potentials can be taken to be $(f,-f)$, which leads to the dual formula (6.1) for $\mathcal W_1$.
--
--   **Formalization Note** $\mathrm{Lip}(f)\le 1$ is `LipschitzWith 1 f`; the conclusion is an equality in `EReal`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §6.1, proof of Proposition 6.1, last display, p. 473

import Mathlib
import Definitions.Def_CompOT_W1_Defs

namespace CompOT.W1

/-- Proof of Proposition 6.1, p. 473 (last display): if `Lip(f) ≤ 1`, then `f^c = -f`, i.e.
`inf_{x ∈ X} [d(x, y) - f(x)] = -f(y)` for every `y`. -/
theorem prop_6_1_cTransform_self {X : Type*} [MetricSpace X] (f : X → ℝ)
    (hf : LipschitzWith 1 f) :
    ∀ y, cTransform f y = ((-f y : ℝ) : EReal) := by sorry

end CompOT.W1
