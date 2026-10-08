-- Prove2me | Theorems.Thm_CompOT_W1_prop_6_1_cTransform_neg
-- name    : CompOT.W1.prop_6_1_cTransform_neg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:34.869308+00:00
-- url     : https://prove2.me/theorems/b10d6c82-0f77-4d61-bb58-f570d9a54c4c
-- title:
--   Proof of Proposition 6.1, pp. 472–473 — if Lip(f) ≤ 1 then g = −f satisfies g^c = f
-- statement:
--   Let $(\mathcal X,d)$ be a metric space with cost $c(x,y)=d(x,y)$ and let $f:\mathcal X\to\mathbb R$ satisfy $\mathrm{Lip}(f)\le1$. Put $g=-f$. Then for every $y\in\mathcal X$,
--
--   $$
--   g^c(y)=\inf_{x\in\mathcal X}\,\bigl[d(x,y)+f(x)\bigr]=f(y).
--   $$
--
--   Hence every 1-Lipschitz function is a $c$-transform, with the explicit choice $g=-f$; this is the "if" half of Proposition 6.1.
--
--   **Formalization Note** $\mathrm{Lip}(f)\le 1$ is `LipschitzWith 1 f`; the infimum is the `EReal` infimum of the $c$-transform definition and the conclusion is an equality in `EReal`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §6.1, proof of Proposition 6.1, second paragraph, pp. 472–473

import Mathlib
import Definitions.Def_CompOT_W1_Defs

namespace CompOT.W1

/-- Proof of Proposition 6.1, pp. 472–473 (second paragraph): if `Lip(f) ≤ 1`, then
`g = -f` satisfies `g^c = f`, i.e. `inf_{x ∈ X} [d(x, y) + f(x)] = f(y)` for every `y`. -/
theorem prop_6_1_cTransform_neg {X : Type*} [MetricSpace X] (f : X → ℝ)
    (hf : LipschitzWith 1 f) :
    ∀ y, cTransform (fun x => -f x) y = (f y : EReal) := by sorry

end CompOT.W1
