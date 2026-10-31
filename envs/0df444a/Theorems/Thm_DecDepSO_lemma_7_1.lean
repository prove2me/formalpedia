-- Prove2me | Theorems.Thm_DecDepSO_lemma_7_1
-- name    : DecDepSO.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:45.632106+00:00
-- url     : https://prove2.me/theorems/d0e84b1a-2183-4820-af81-11110a0c380e
-- title:
--   Lemma 7.1 — approximate subgradient inequality $f(\bar x)\ge f(x)+\langle\mathbb E[g(x)],\bar x-x\rangle+\frac{\alpha(1-2\rho)}2\|x-\bar x\|^2$
-- statement:
--   Assume parts (a)–(b) of Assumption 7: $f$ is $\alpha$-strongly convex and differentiable with $L$-Lipschitz gradient, $r$ is proper, closed and convex, $\bar x$ minimizes $\varphi=f+r$, and $L,B,\alpha>0$; set $\rho:=B/\alpha$. Let $x\in E$ and let $v\in E$ satisfy the bias bound of Assumption 7 (c),
--   $$
--   \|v-\nabla f(x)\|\le B\|x-\bar x\|
--   $$
--   (for instance $v=\mathbb E[g(x)]$). Then
--   $$
--   f(\bar x)\ \ge\ f(x)+\langle v,\bar x-x\rangle+\frac{\alpha(1-2\rho)}{2}\|x-\bar x\|^2 .
--   $$
--
--   Strong convexity of $f$ survives replacing the gradient by a biased estimate, with the modulus reduced from $\alpha$ to $\alpha(1-2\rho)=\alpha-2B$. Lemma 7.2 applies it with $v=\mathbb E_t[g_t]$.
--
--   **Formalization Note** $\rho$ is written out as $B/\alpha$.
--
--   Differences from the source:
--   - generalization: E[g(x)], the mean of the oracle at x → any vector v with ‖v − ∇f(x)‖ ≤ B‖x − x̄‖; reason: the lemma uses only the bias bound of Assumption 7 (c), which E[g(x)] satisfies.
--   - encoding: Rd, "a Euclidean space" (p.5) → a finite-dimensional real inner product space E; reason: every such space is isometric to some Rd and the paper calls Rd a Euclidean space.
--   - encoding: r: Rd → R ∪ {∞} closed and convex → the pair (D, r) with GoldenRatioVI.IsProperConvexLsc D r; reason: closed = lower semicontinuous extension; D ≠ ∅ is implicit because φ has a minimizer x̄ ∈ dom r.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Lemma 7.1, p.25

import Mathlib
import Definitions.Def_DecDepSO_Assumption7ab

namespace DecDepSO

/-- **Lemma 7.1 (Approximate subgradient inequality).**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, Lemma 7.1, p.25: "Under Assumption 7, it holds that
f(x̄) ≥ f(x) + ⟨E[g(x)], x̄ − x⟩ + α(1 − 2ρ)/2 ‖x − x̄‖² ∀x ∈ Rd", where ρ := B/α.

For every point `x` and every vector `v` within `B‖x − x̄‖` of `∇f(x)` (in particular the oracle
mean `v = E[g(x)]`),
`f(x̄) ≥ f(x) + ⟨v, x̄ − x⟩ + α(1 − 2B/α)/2 · ‖x − x̄‖²`.

**Formalization Note.** `E[g(x)]` is replaced by an arbitrary vector `v` satisfying the bias
bound of Assumption 7 (c), which is all the lemma uses; the lemma is applied with
`v = E_t[g_t](ω)` in Lemma 7.2. `ρ` is written out as `B / α`. -/
theorem lemma_7_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {D : Set E} {r : E → ℝ} {L B α : ℝ} {xbar : E}
    (hA : Assumption7ab f D r L B α xbar) (x v : E)
    (hv : ‖v - gradient f x‖ ≤ B * ‖x - xbar‖) :
    f xbar ≥ f x + inner ℝ v (xbar - x) + α * (1 - 2 * (B / α)) / 2 * ‖x - xbar‖ ^ 2 := by sorry

end DecDepSO
