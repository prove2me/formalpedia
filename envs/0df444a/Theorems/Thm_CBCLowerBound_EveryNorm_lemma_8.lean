-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_lemma_8
-- name    : CBCLowerBound.EveryNorm.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:55.723211+00:00
-- url     : https://prove2.me/theorems/7b0d3020-2ee4-4cf6-bdc1-41966b3f86f5
-- title:
--   Lemma 8 — $W_1(P,Q)\le 8\,\|\sum_v (Q(v)-P(v))\Psi(v)\|_1$ on consecutive requests
-- statement:
--   Fix admissible parameters, a tie rule and a level $r$, and let $S,S'$ be consecutive requests (possibly equal) of a sequence in the support of $D_r$ on $G=G_r$. For probability distributions $P$ on $S$ and $Q$ on $S'$, extended by zero to all vertices of $G$,
--   $$W_1(P,Q)\le 8\,\Big\|\sum_{v\in G}\big(Q(v)-P(v)\big)\Psi(v)\Big\|_1\qquad\text{(eq. (9))},$$
--   where $W_1$ is the optimal transportation cost for the metric $d_G$ and $\|x\|_1=\sum_{i=1}^{2r+1}|x_i|$.
--
--   The lemma converts movement of weighted averages $\sum_v P(v)\Psi(v)$ in $\mathbb R^{2r+1}$, which is what a convex body chasing algorithm pays, into transportation cost on the discrete instance, which is what Lemma 3 bounds from below.
--
--   Differences from the source:
--   - encoding: ‖·‖₁ of a vector of ℝ^D → the sum of absolute values of its 2r+1 coordinates; reason: definition of the ℓ₁ norm
--   - encoding: a realized level-r request sequence → a list of annotated requests in the support of the PMF D_r, read through its plain sets; reason: the annotation records the call structure and does not change the requested sets
--   - reading: "a fixed rule to break a tie" (Stage 3) → the statement holds for both fixed rules (tie : Bool); reason: the paper does not specify the rule
--   - reading: "the final request of this stage consists of the two current vertices" (Stage 2) → the last request of the last Stage-2 call, no extra request; reason: that last request is exactly the pair of current vertices
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.12, Lemma 8, eq. (9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Requests

namespace CBCLowerBound.EveryNorm

/-- **Lemma 8** (transportation cost is controlled by weighted average movement; Christianson,
STOC 2027 #674, p.12). Let `S, S'` be consecutive requests (possibly equal) of a sequence in the
support of `D_r` (any parameters, tie rule, level `r`). For probability distributions `P` on `S`
and `Q` on `S'`, extended by zero elsewhere,
`W₁(P, Q) ≤ 8 ‖∑_{v ∈ G} (Q(v) − P(v)) Ψ(v)‖₁` (eq. (9)). -/
theorem lemma_8 (θ : Params) (tie : Bool) (r : ℕ) (σ : List (AReq θ r))
    (hσ : σ ∈ (reqDist θ tie r).support) (t : ℕ) (ht : t + 1 < σ.length)
    (P Q : Vert θ r → ℝ) (hP : IsProbVec P) (hQ : IsProbVec Q)
    (hPS : ∀ v ∉ (σ[t]).set, P v = 0) (hQS : ∀ v ∉ (σ[t + 1]).set, Q v = 0) :
    W1 (dist θ r) P Q ≤ 8 * ∑ i : Fin (2 * r + 1), |∑ v, (Q v - P v) * Psi θ r v i| := by sorry

end CBCLowerBound.EveryNorm
