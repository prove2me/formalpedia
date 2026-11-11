-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_2_4
-- name    : ArbLindbladLearn.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:22:22.029474+00:00
-- url     : https://prove2.me/theorems/879d60b2-ffac-4115-b738-0e68cd4d9a46
-- title:
--   Lemma 2.4 — endpoint interpolation error
-- statement:
--   Let $q\in\mathbb N_{>0}$, $K>0$ and $T=1/K$, and let $t_0,\dots,t_q$ be the Chebyshev–Lobatto nodes on $[0,T]$, with $p_q'(0)=\sum_{j=0}^q\ell_j'(0)f(t_j)$.
--   1. If $f:\mathbb R_{\ge0}\to\mathbb R$ is $(q+1)$ times differentiable and $|f^{(q+1)}(x)|\le K^{q+1}$ for $x\ge0$, then
--   $$|f'(0)-p_q'(0)|\le\frac{K}{(q+1)!}.$$
--   2. If $f:\mathbb R_{\ge0}\to\mathbb C$ satisfies the same derivative bound, then $|f'(0)-p_q'(0)|\le\sqrt2K/(q+1)!$.
--
--   This is the interpolation-bias bound used in both stages of the learner.
--
--   Differences from the source:
--   - encoding: f : ℝ≥0 → ℝ (or ℂ), (q + 1) times differentiable, derivatives one-sided at 0 → f on ℝ with iteratedDerivWithin on Set.Ici 0, the derivatives of orders 0, …, q differentiable on [0, ∞); reason: values off [0, ∞) do not enter any hypothesis or the conclusion; these are the same functions
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 2.4, p.16

import Mathlib
import Definitions.Def_ArbLindbladLearn_lagDeriv0

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn



/-- Lemma 2.4 (Endpoint interpolation error; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.16). Let
`f : ℝ_{≥0} → ℝ` be `(q + 1)` times differentiable with `|f^{(q+1)}(x)| ≤ K^{q+1}` for some `K > 0`.
Mapping `q + 1` Chebyshev–Lobatto nodes to `[0, T]` with `T = 1/K` gives
`|f′(0) − p′_q(0)| ≤ K/(q + 1)!`. For a complex-valued `f : ℝ_{≥0} → ℂ` with the same derivative
bound, the bound is `√2 K/(q + 1)!`.

**Formalization Note** `q ∈ ℕ_{>0}` (Definition 2.10). The domain `ℝ_{≥0}` is `Set.Ici 0`: `f` is a
function on `ℝ` whose values off `[0, ∞)` are irrelevant, its derivatives are one-sided at `0`
(`iteratedDerivWithin … (Set.Ici 0)`), "`(q+1)` times differentiable" means that the derivatives of
orders `0, …, q` are differentiable on `[0, ∞)`, and the derivative bound holds on `[0, ∞)`.
`p′_q(0) = Σ_{j=0}^q ℓ′_j(0) f(t_j)` is `endpointRule`. -/
theorem lemma_2_4 (q : ℕ) (hq : 0 < q) (K : ℝ) (hK : 0 < K) :
    (∀ f : ℝ → ℝ,
      (∀ k ≤ q, DifferentiableOn ℝ (iteratedDerivWithin k f (Set.Ici 0)) (Set.Ici 0)) →
      (∀ x : ℝ, 0 ≤ x → |iteratedDerivWithin (q + 1) f (Set.Ici 0) x| ≤ K ^ (q + 1)) →
      |derivWithin f (Set.Ici 0) 0 - endpointRule q (1 / K) f| ≤ K / (q + 1).factorial) ∧
    (∀ f : ℝ → ℂ,
      (∀ k ≤ q, DifferentiableOn ℝ (iteratedDerivWithin k f (Set.Ici 0)) (Set.Ici 0)) →
      (∀ x : ℝ, 0 ≤ x → ‖iteratedDerivWithin (q + 1) f (Set.Ici 0) x‖ ≤ K ^ (q + 1)) →
      ‖derivWithin f (Set.Ici 0) 0 - endpointRuleC q (1 / K) f‖ ≤
        Real.sqrt 2 * K / (q + 1).factorial) := by sorry

end ArbLindbladLearn
