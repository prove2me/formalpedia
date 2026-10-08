-- Prove2me | Theorems.Thm_BalkemaDeHaan_FiniteT_lemma_4
-- name    : BalkemaDeHaan.FiniteT.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:44.180187+00:00
-- url     : https://prove2.me/theorems/5283078f-b304-4375-8f09-357f97dee8ed
-- title:
--   Lemma 4 — 0 ≤ −(∂/∂c)Π_{0,c}(x) < 1 for c > −1, x ≠ 0, cx ≠ −1
-- statement:
--   Let $c > -1$ and let $x$ be real with $x \ne 0$ and $cx \ne -1$. Then $c \mapsto \Pi_{0,c}(x)$ is differentiable at $c$, and
--   $$
--   0 \le -\frac{\partial}{\partial c}\Pi_{0,c}(x) < 1 .
--   $$
--   Thus, at fixed $x$, the family $\Pi_{0,c}(x)$ is nonincreasing in $c$ and moves by less than the change of the parameter; this is what makes the approximation in the Corollary to Theorem 7 uniform with error $\varepsilon$.
--
--   **Formalization Note** Differentiability is part of the conclusion: there is $d$ with `HasDerivAt (fun c' => Π_{0,c'}(x)) d c` and $0 \le -d < 1$. At $c = 0$ the derivative is taken across the case split of the definition of $\Pi_{0,c}$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 802 (PDF 11), Lemma 4

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0

namespace BalkemaDeHaan.FiniteT

/-- Lemma 4, p. 802: `0 ≤ -(∂/∂c) Π_{0,c}(x) < 1` for `c > -1` if `x ≠ 0` and `c x ≠ -1`;
in particular `c ↦ Π_{0,c}(x)` is differentiable at such `c`. -/
theorem lemma_4 (c x : ℝ) (hc : -1 < c) (hx : x ≠ 0) (hcx : c * x ≠ -1) :
    ∃ d : ℝ, HasDerivAt (fun c' : ℝ => pi0 c' x) d c ∧ 0 ≤ -d ∧ -d < 1 := by sorry

end BalkemaDeHaan.FiniteT
