-- Prove2me | Theorems.Thm_DaiWeissFluid_KellyType_condition_b
-- name    : DaiWeissFluid.KellyType.condition_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:21:57.470706+00:00
-- url     : https://prove2.me/theorems/108a4698-441c-466c-a6cc-20031ec1820c
-- title:
--   Proof of Theorem 6.1 — an empty station has the smaller Lyapunov component (condition (b))
-- statement:
--   Let a two-station reentrant line have no immediate feedback ($\sigma(k+1) \ne \sigma(k)$), positive mean service times, and any number $K$ of classes; the route may start at either station. Let $(Q,T)$ be a fluid model solution and $G_i(t) = \sum_{k \in C_i} Q_k^+(t)$. For every $t \ge 0$ and the two stations $i \ne j$,
--
--   $$ W_i(t) = 0 \ \Longrightarrow\ G_i(t) \le G_j(t), $$
--
--   with equality $G_i(t) = G_j(t)$ when, in addition, the route starts at station $j$ ($\sigma(1) = j$) and ends at station $i$ ($\sigma(K) = i$).
--
--   For $K = 2n$ with the route starting at station 1, this is the paper's pair: when $W_1(t) = 0$, $G_1(t) = \sum_{l=2}^n Q^+_{2l-2}(t) \le \sum_{l=1}^n Q^+_{2l}(t) = G_2(t)$, and when $W_2(t) = 0$, $G_2(t) = \sum_{l=1}^n Q^+_{2l-1}(t) = G_1(t)$. It is condition (b) of Lemma 3.2 for the Lyapunov components of Theorem 6.1.
--
--   **Formalization Note** The statement covers both parities of $K$ (the paper treats $K = 2n$ and says $K = 2n+1$ "can be proved similarly") and both starting stations. Kelly type is not needed for this step. Indices are 0-based.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 130, proof of Theorem 6.1 ("When W₁(t) = 0, …")

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_KellyType_KellyLine

namespace DaiWeissFluid.KellyType

/-- Proof of Theorem 6.1, p. 130: in a two-station reentrant line without immediate feedback
(any number `K` of classes, the route starting at either station), along every fluid solution and
for `t ≥ 0`, if station `i` is empty (`W_i(t) = 0`) then `G_i(t) ≤ G_j(t)` for the other
station `j`, where `G_i(t) = ∑_{k ∈ C_i} Q_k⁺(t)`; and `G_i(t) = G_j(t)` when moreover the route
starts at `j` and ends at `i` (for `K = 2n` starting at station 1 this is the printed
`W₂(t) = 0 ⇒ G₂(t) = G₁(t)`). -/
theorem condition_b {K : ℕ} (L : ReentrantLine 2 K) (hm : ∀ k, 0 < L.m k)
    (hfb : L.NoImmediateFeedback)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T) (t : ℝ) (ht : 0 ≤ t)
    (i j : Fin 2) (hij : i ≠ j) :
    L.volume Q i t = 0 →
      L.kellyG Q i t ≤ L.kellyG Q j t ∧
        ((hK : 0 < K) → L.σ ⟨0, hK⟩ = j → L.σ ⟨K - 1, by omega⟩ = i →
          L.kellyG Q i t = L.kellyG Q j t) := by sorry

end DaiWeissFluid.KellyType
