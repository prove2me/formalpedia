-- Prove2me | Theorems.Thm_EvenCycleTuran_C4Count_theorem_11
-- name    : EvenCycleTuran.C4Count.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:21.52899+00:00
-- url     : https://prove2.me/theorems/6dc92d6d-6d6f-4907-a925-9d027f407ef5
-- title:
--   Theorem 11 — ex(n, C₄, C₂ₖ) = (1 + o(1))(k−1)(k−2)n²/4 for k ≥ 2
-- statement:
--   For an integer $k\ge 2$ let $\mathrm{ex}(n,C_4,C_{2k})$ be the maximum number of copies of the four-cycle $C_4$ in a graph on $n$ vertices that contains no cycle of length $2k$. Then
--
--   $$\mathrm{ex}(n,C_4,C_{2k})=(1+o(1))\,\frac{(k-1)(k-2)}{4}\,n^2 \qquad (n\to\infty).$$
--
--   The lower bound is attained by the complete bipartite graph $K_{k-1,n-k+1}$. The theorem determines the maximum number of four-cycles in a $C_{2k}$-free graph asymptotically, including its leading constant $\frac{(k-1)(k-2)}4$.
--
--   **Formalization Note** The $o(1)$ is a real sequence $\varepsilon(n)\to 0$ (depending on $k$, fixed before $n$), and the equality holds for all sufficiently large $n$; this is the literal form of "$(1+o(1))$" and, unlike a ratio limit, keeps its content at $k=2$, where it says $\mathrm{ex}(n,C_4,C_4)=0$. Copies are unlabelled (Mathlib's `copyCount`); $\mathrm{ex}$ is `exCyc n (cycleGraph 4) {2 * k}`, a true maximum.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 6, Theorem 11 (restated and proved on p. 12, §4.1)

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting
open Finset SimpleGraph Filter Topology

namespace EvenCycleTuran.C4Count

/-- Theorem 11, p. 6: for `k ≥ 2`, ex(n, C₄, C₂ₖ) = (1 + o(1)) (k−1)(k−2)/4 · n². -/
theorem theorem_11 (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, (exCyc n (cycleGraph 4) {2 * k} : ℝ) =
        (1 + ε n) * (((k : ℝ) - 1) * ((k : ℝ) - 2) / 4 * (n : ℝ) ^ 2) := by sorry

end EvenCycleTuran.C4Count
