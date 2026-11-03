-- Prove2me | Theorems.Thm_EnvelopeMSLP_lemma_2
-- name    : EnvelopeMSLP.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:41.650981+00:00
-- url     : https://prove2.me/theorems/04f9e328-fc20-4b66-931f-9193a8755511
-- title:
--   Lemma 2 — the post-decision value is concave and piecewise linear
-- statement:
--   Let $\xi$ be finitely supported, and fix $\theta$ and a node of the history tree. The post-decision value $x\mapsto\bar V(x)$ at that node has finitely many affine functions $a_j$ and a polyhedron $Q=\{x:Gx\le g\}$ with
--   $$\bar V(x)=\min_j a_j(x)\ \text{ on }Q,\qquad\bar V(x)=-\infty\ \text{ off }Q,$$
--   where the minimum over no functions is $+\infty$. Moreover $\bar V$ is concave: $u\bar V(x)+v\bar V(y)\le\bar V(ux+vy)$ for $u,v\ge0$, $u+v=1$.
--
--   This is what lets a stage problem (8) be written as a linear program.
--
--   **Formalization Note** Values are in `EReal`. The value $+\infty$ really occurs, when a stage problem is unbounded, and the paper assumes no finiteness.
--
--   Differences from the source:
--   - reading: x_t ↦ V̄_t(x_t, ξ_t, θ) as printed → V̄_{t+1}(x_t, ξ^t, θ) of the definition just above the lemma, at every node; reason: the printed indices slip: the definition on p.12 is V̄_{t+1} and conditions on the history
--   - reading: a concave, piece-wise linear function → a finite minimum of affine functions on a polyhedron, ⊥ off it, and concavity in EReal; reason: p.12 says a minimum of finitely many affine functions; the extended values must be placed because no finiteness is assumed
--   - generalization: levels V̄_{t+1}, t ∈ [T] → also level 0, the expectation of the first-stage value; reason: the extra level is more of the same; levels 1 to T are the source's
--   - encoding: a discrete process ξ on a probability space (Ω, F, P) → a finite scenario type Ω with p(ω) > 0 summing to 1; reason: this is the support of the law of ξ (p.12: finitely many atoms); a general space pushes forward onto it and the statement sees only the law
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Lemma 2, p.12

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_postValue
open Matrix

namespace EnvelopeMSLP

/-- **Lemma 2: the post-decision value is concave and piecewise linear.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), Lemma 2, p.12, for the
object `V̄_{t+1}(x_t, ξ^t, θ)` defined above it. At every level `i`, node and `θ`, there are finitely many
affine functions `a_j` and a polyhedron `Q = {G x ≤ g}` with `V̄(x) = min_j a_j(x)` on `Q` and `V̄(x) = ⊥` off
`Q`, and `V̄` is concave along segments in `EReal`.

**Formalization Note.** Values are in `EReal`. The minimum over no affine function is `⊤`, which occurs
when a stage LP is unbounded. -/
theorem lemma_2 {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (i : Fin (T + 1)) (ω : Ω) :
    (∃ (k q : ℕ) (a : Fin k → Fin (P.n i) → ℝ) (β : Fin k → ℝ)
        (G : Matrix (Fin q) (Fin (P.n i)) ℝ) (g : Fin q → ℝ),
      (∀ x, G *ᵥ x ≤ g → P.postValue θ i x ω = ⨅ j, ((a j ⬝ᵥ x + β j : ℝ) : EReal)) ∧
      ∀ x, ¬ G *ᵥ x ≤ g → P.postValue θ i x ω = ⊥) ∧
    ∀ (x y : Fin (P.n i) → ℝ) (u v : ℝ), 0 ≤ u → 0 ≤ v → u + v = 1 →
      (u : EReal) * P.postValue θ i x ω + (v : EReal) * P.postValue θ i y ω ≤
        P.postValue θ i (u • x + v • y) ω := by sorry

end EnvelopeMSLP
