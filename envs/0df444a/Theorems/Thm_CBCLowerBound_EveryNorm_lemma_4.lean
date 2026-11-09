-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_lemma_4
-- name    : CBCLowerBound.EveryNorm.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:52.960988+00:00
-- url     : https://prove2.me/theorems/b4dceae7-f58a-4548-b4db-4ab376bbba08
-- title:
--   Lemma 4 — every coordinate of $\Psi$ is 1-Lipschitz: $\|\Psi(u)-\Psi(v)\|_\infty\le d_G(u,v)$
-- statement:
--   Fix admissible parameters and a level $r\ge0$, let $G=G_r$ with shortest-path metric $d_G$, and let $\Psi:G\to\mathbb R^{2r+1}$ be the map of eq. (5), $\Psi(v)=(h(v),(\psi_{s,L}(v),\psi_{s,R}(v))_{s=1}^r)$. Every scalar coordinate of $\Psi$ is $1$-Lipschitz in graph distance: for every coordinate $i$ and all vertices $u,v$, $|\Psi(u)_i-\Psi(v)_i|\le d_G(u,v)$. In particular,
--   $$\|\Psi(u)-\Psi(v)\|_\infty\le d_G(u,v)\qquad\text{(eq. (6))}.$$
--
--   With the norm comparison $\|x\|_p\le D^{1/p}\|x\|_\infty$ this bounds the offline cost of the mapped convex instance (Proposition 9).
--
--   Differences from the source:
--   - encoding: coordinates (h, ψ_{1,L}, ψ_{1,R}, …) of ℝ^D → 0-based indices of Fin (2r+1) → ℝ (0 is h, 2s−1 is ψ_{s,L}, 2s is ψ_{s,R}) with the sup norm; reason: Lean indexing and Mathlib's norm on functions; same vectors and norm
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.9, Lemma 4, eq. (6), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Graph

namespace CBCLowerBound.EveryNorm

/-- **Lemma 4** (coordinatewise movement bound; Christianson, STOC 2027 #674, p.9). For every
parameter choice `θ` and level `r`, every scalar coordinate of `Ψ` is `1`-Lipschitz in the
graph distance of `G = G_r`; in particular `‖Ψ(u) − Ψ(v)‖_∞ ≤ d_G(u, v)` (eq. (6)). -/
theorem lemma_4 (θ : Params) (r : ℕ) :
    (∀ (i : Fin (2 * r + 1)) (u v : Vert θ r), |Psi θ r u i - Psi θ r v i| ≤ dist θ r u v) ∧
    ∀ u v : Vert θ r, ‖Psi θ r u - Psi θ r v‖ ≤ dist θ r u v := by sorry

end CBCLowerBound.EveryNorm
