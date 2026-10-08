-- Prove2me | Theorems.Thm_DaiWeissFluid_KellyType_theorem6_1
-- name    : DaiWeissFluid.KellyType.theorem6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:23:10.131986+00:00
-- url     : https://prove2.me/theorems/814778f2-d559-4b74-91fd-43829525af94
-- title:
--   Theorem 6.1 — without immediate feedback, the work-conserving fluid model of a two-station Kelly-type line is stable
-- statement:
--   Consider a reentrant line with two stations and $K$ classes, with positive mean service times $m_k$, which is of **Kelly type**: every visit to station $i$ has the same mean service time $\beta_i$, $m_k = \beta_{\sigma(k)}$. Assume the routing has **no immediate feedback**, $\sigma(k+1) \ne \sigma(k)$ for $k = 1, \dots, K-1$, and the traffic condition (1.7), $\rho_i = \sum_{k \in C_i} m_k < 1$ for $i = 1,2$. Then the work-conserving fluid model (1.8)–(1.13) is stable: there is $\delta > 0$ such that every work-conserving fluid solution with $|Q(0)| = 1$ satisfies
--
--   $$ Q_k(t) = 0 \qquad \text{for all } t \ge \delta \text{ and } k = 1,\dots,K. $$
--
--   The paper's Theorem 6.1 reads: "Consider a two station Kelly-type reentrant network. Assume that routing does not have immediate feedback. Then any work-conserving policy is stable." It asserts stability of every work-conserving policy; its proof establishes the fluid-model stability formalized here, and the queueing-level conclusion follows from Theorem 1.1 of the paper (Dai 1995, Thm 4.3), which is cited and not formalized. Since every work-conserving policy's fluid model is a subset of the work-conserving fluid model, the statement covers all such policies at once. Both hypotheses are needed: Remark 2 of the paper gives a Kelly-type two-station line with immediate feedback that is unstable under a static priority, and Remark 3 a three-station counterexample.
--
--   **Formalization Note** Indices are 0-based. The statement holds for every $K$, of either parity, and the route may begin at either station; the paper proves $K = 2n$ and says $K = 2n+1$ "can be proved similarly". $m_k > 0$ is an explicit hypothesis (the paper takes it for granted, as $m_k$ are means of service times). Stability is Definition 1.3, which only constrains solutions with $|Q(0)| = \sum_k Q_k(0) = 1$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 130, Theorem 6.1

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_KellyType_KellyLine

namespace DaiWeissFluid.KellyType

/-- Theorem 6.1, p. 130: in a two-station Kelly-type reentrant line (station means `β`) whose
route has no immediate feedback, under the traffic condition (1.7), the work-conserving fluid
model (1.8)–(1.13) is stable in the sense of Definition 1.3. -/
theorem theorem6_1 {K : ℕ} (L : ReentrantLine 2 K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) (β : Fin 2 → ℝ) (hkelly : L.IsKellyType β)
    (hfb : L.NoImmediateFeedback) :
    DaiWeissFluid.ThreeBuffer.FluidStable L.IsWorkConserving := by sorry

end DaiWeissFluid.KellyType
