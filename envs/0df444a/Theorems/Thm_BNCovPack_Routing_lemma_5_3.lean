-- Prove2me | Theorems.Thm_BNCovPack_Routing_lemma_5_3
-- name    : BNCovPack.Routing.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:37:41.041104+00:00
-- url     : https://prove2.me/theorems/317f3f09-728d-4fe2-bf76-e0b080af392a
-- title:
--   Lemma 5.3 — Φ ≤ 1 initially, Φ > 0, and serving on some flow path or rejecting never increases Φ
-- statement:
--   Let $E$ be a non-empty finite set of $m$ edges with capacities $u(e) > 0$, let $B = \exp(1 + \ln(2m)/u(\min)) - 1$, and let $\Phi(T, L, \chi, s)$ be the potential of Section 5.2. Then:
--
--   1. initially ($T = 0$, $L = 0$, $\chi = 0$, $s = 0$), $\Phi \le 1$;
--   2. $\Phi > 0$ in every state;
--   3. consider any state $(T, L, \chi, s)$ and a request with paths $P_1, \dots, P_k$ whose flows are raised by $g_1, \dots, g_k \ge 0$ with $\sum_j g_j \le 1$, so that $T' = T + \sum_j g_j$ and $L'_e = L_e + \sum_{j : e \in P_j} g_j$. Then
--
--   $$
--   \exists j:\ g_j > 0 \ \text{and}\ \Phi\big(T', L', \chi + \mathbf 1_{P_j}, s+1\big) \le \Phi(T, L, \chi, s) \quad \text{or} \quad \Phi(T', L', \chi, s) \le \Phi(T, L, \chi, s).
--   $$
--
--   In words: each time the flow of a request is increased, either serving the request on one of its flow paths (a path whose flow was raised) or rejecting it does not increase the potential. This is what makes the online rounding rule well defined and keeps $\Phi \le 1$ throughout the run.
--
--   **Formalization Note** The third claim is stated for an arbitrary state and an arbitrary admissible flow increase, which is what the paper's argument uses ($g_j \ge 0$, $\sum_j g_j \le 1 \le B$). The existence ranges over the request's flow paths, the paths $P_j$ with $g_j > 0$, as on the page ("serving the request on some flow path").
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 15, Lemma 5.3 (proof pp. 15–16)

import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_Potential
import Definitions.Def_BNCovPack_Routing_Algorithm

namespace BNCovPack.Routing

/-- Lemma 5.3, Buchbinder–Naor 2009, p. 15. Let `E` be a non-empty finite set of `m` edges with
capacities `u e > 0`, and `B = exp(1 + ln(2m)/u(min)) − 1`.
1. Initially (no flow, no edge used, no request served) `Φ ≤ 1`.
2. `Φ > 0` in every state.
3. Let a request with path list `ps` have its flows raised by `g` (`g[j] ≥ 0` on the `j`-th path,
   `∑_j g[j] ≤ 1`), from any state with total flow `T`, edge loads `L`, edge usage `χ` and `s`
   served requests. Then either serving the request on some flow path (a path `ps[j]` with
   `g[j] > 0`), or rejecting it, gives a potential (computed with the raised flows) at most the
   potential before the increase. -/
theorem lemma_5_3 {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E] (u : E → ℝ)
    (hu : ∀ e, 0 < u e) :
    potential u (roundingScale u) 0 (fun _ => 0) (fun _ => 0) 0 ≤ 1 ∧
    (∀ (T : ℝ) (L : E → ℝ) (χ : E → ℕ) (s : ℕ), 0 < potential u (roundingScale u) T L χ s) ∧
    ∀ (T : ℝ) (L : E → ℝ) (χ : E → ℕ) (s : ℕ) (ps : List (Finset E)) (g : List ℝ),
      g.length = ps.length → (∀ y ∈ g, 0 ≤ y) → g.sum ≤ 1 →
      (∃ Py ∈ ps.zip g, 0 < Py.2 ∧
          potential u (roundingScale u) (T + g.sum) (fun e => L e + pathLoad e ps g)
            (addPath χ Py.1) (s + 1) ≤ potential u (roundingScale u) T L χ s) ∨
      potential u (roundingScale u) (T + g.sum) (fun e => L e + pathLoad e ps g) χ s ≤
        potential u (roundingScale u) T L χ s := by sorry

end BNCovPack.Routing
