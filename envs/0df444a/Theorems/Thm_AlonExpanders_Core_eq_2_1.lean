-- Prove2me | Theorems.Thm_AlonExpanders_Core_eq_2_1
-- name    : AlonExpanders.Core.eq_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:46:16.853534+00:00
-- url     : https://prove2.me/theorems/42317673-6ddb-4a63-abbd-589f1f69cecd
-- title:
--   Eq. (2.1) — the positive part $g$ of a $\lambda(G)$-eigenvector satisfies $\lambda \ge \sum_{uv\in E}(g(u)-g(v))^2/\sum_v g^2(v)$
-- statement:
--   Let $G = (V, E)$ be a finite simple graph on $n \ge 2$ vertices, with Laplacian $Q = \mathrm{diag}(d(v)) - A_G$, and let $\lambda = \lambda(G)$ be the second-smallest eigenvalue of $Q$, counted with multiplicity. Let $f : V \to \mathbb{R}$, $f \ne 0$, be an eigenvector of $Q$ for $\lambda$, that is $(Qf)(v) = \lambda f(v)$ for all $v \in V$, and let $g : V \to \mathbb{R}$ be its positive part,
--
--   $$
--   g(v) = \begin{cases} f(v) & \text{if } f(v) > 0, \\ 0 & \text{otherwise.} \end{cases}
--   $$
--
--   Then
--
--   $$
--   \sum_{uv \in E} \bigl(g(u) - g(v)\bigr)^2 \;\le\; \lambda \sum_{v \in V} g^2(v),
--   $$
--
--   where the left-hand sum runs over the edges of $G$, each counted once. Equivalently, whenever $g \ne 0$, $\lambda \ge \sum_{uv \in E} (g(u)-g(v))^2 / \sum_{v} g^2(v)$.
--
--   This is the first step of the proof of Lemma 2.4: it reduces the lower bound on $\lambda$ to a lower bound on the Dirichlet quotient of a nonnegative function supported on the positive set of $f$.
--
--   **Formalization Note** The inequality is stated in multiplied form, which agrees with the paper's quotient whenever $\sum_v g^2(v) > 0$ and avoids division by zero otherwise. The sum over edges is written as half the sum over ordered adjacent pairs $(u, v)$. $Q$ is Mathlib's `G.lapMatrix ℝ` and $\lambda$ the published `AlonMilman.Diameter.lambda1`; $n \ge 2$ is the range in which $\lambda(G)$ exists. The paper's normalisation $0 < |V^+| \le n/2$ is not assumed.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 87, Eq. (2.1) (setup in the proof of Lemma 2.4, p. 86)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

namespace AlonExpanders.Core

/-- Eq. (2.1) of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 87 (setup p. 86).
Let `f` be an eigenvector of `Q_G = diag(d(v)) − A_G` for `λ = λ(G)` and `g = max(f, 0)` its
positive part. Then `λ ≥ Σ_{uv∈E} (g(u) − g(v))² / Σ_v g²(v)`, stated in multiplied form; each
edge is counted once, hence the factor `1/2` in front of the sum over ordered adjacent pairs. -/
theorem eq_2_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (f : V → ℝ) (hf0 : f ≠ 0)
    (hf : Matrix.mulVec (G.lapMatrix ℝ) f = AlonMilman.Diameter.lambda1 G • f) :
    (1 / 2 : ℝ) * ∑ u, ∑ v, (if G.Adj u v then (max (f u) 0 - max (f v) 0) ^ 2 else 0) ≤
      AlonMilman.Diameter.lambda1 G * ∑ v, (max (f v) 0) ^ 2 := by sorry

end AlonExpanders.Core
