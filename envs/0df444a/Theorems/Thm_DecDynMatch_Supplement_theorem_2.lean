-- Prove2me | Theorems.Thm_DecDynMatch_Supplement_theorem_2
-- name    : DecDynMatch.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:32:59.882435+00:00
-- url     : https://prove2.me/theorems/14916d58-50ff-4d6f-a5e6-8be99e28eab6
-- title:
--   Theorem 2 — $D_{\Pi_g}(T;I)=O(g(t^*)+K^2N_g(T))$ for every feasible $g$
-- statement:
--   Let $g$ be a feasible growth function and $\Pi_g$ the protocol SC-DA with replay length $L\leftarrow F_g(a-\ell)$, where $s_0=H$, $s_{j+1}=s_j+g(s_j)$ and
--   $$
--   F_g(x)=H+2x+\max\bigl(\{g(s_j)-s_j: j\ge0,\ 64s_j\le x\}\cup\{0\}\bigr),\qquad N_g(T)=\#\{j\ge0: s_j<T\}.
--   $$
--   Then there is a constant $C$, depending only on $g$, such that for every number of arms $K\ge2$, every dynamic matching instance $I$ with last population-event time $t^*$ and every horizon $T>H=4(K^2+5K+1)+4$,
--   $$
--   D_{\Pi_g}(T;I)\le C\bigl(g(t^*)+K^2N_g(T)\bigr).
--   $$
--   Here $D_{\Pi_g}(T;I)$ counts the rounds $1\le t\le T$ in which the realized matching differs from the player-optimal stable matching of that round.
--
--   The bound expresses the trade-off between convergence speed and asymptotic cost: faster-growing $g$ makes recovery after the last population event slower (the term $g(t^*)$) but maintenance cheaper ($N_g(T)$ grows more slowly). With $g(t)=t$ it gives Theorem 1.
--
--   **Formalization Note** $\Pi_g$ is the base execution `exec` with replay rule `Fg K g`, so $D_{\Pi_g}(T;I)$ is the base `D (Fg K g) I T` and $N_g$ is the base `Ng`. The final market may be empty.
--
--   Differences from the source:
--   - generalization: g feasible: non-decreasing, Ω(t) and polynomial-time computable → Feasible g without polynomial-time computability; reason: no bound uses computability (it only serves the running time of evaluating F_g, p.21); every feasible g of the paper satisfies Feasible, so the Lean statement specializes to the paper's
--   - encoding: D_{Π_g}(T; I) = O(g(t*) + K² N_g(T)) → ∀ g, Feasible g → ∃ C, ∀ K ι I T, H K < T → D (Fg K g) I T ≤ C (g(t*) + K² Ng K g T); reason: the O-constant depends only on g (App. A.5, p.21, eq. (32)); Π_g is the base execution with replay rule F_g
--   - encoding: utilities μ, π in [0, 1] → arbitrary injective real utilities (base Instance); reason: the protocol and the POSM depend only on the rankings; every [0, 1] instance is an instance
--   - generalization: instances with a non-empty final market P_{t*} ≠ ∅ ("Wlog", §2.3, p.5) → every instance, the final market may be empty; reason: with an empty final market both matchings are empty from round t* on, so the extra instances add no mismatch after t*; on the paper's instances the statement is the paper's
--   - encoding: g : ℕ≥1 → ℕ≥1 → g : ℕ → ℕ with the conditions of Feasible on t ≥ 1; reason: g(0) is never read (s₀ = H ≥ 1 and t* ≥ 1)
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Theorem 2, p.9, eq. (7); §3.2, p.8; App. A.5, pp.20–21

import Mathlib
import Definitions.Def_DecDynMatch_Fg
import Definitions.Def_DecDynMatch_D
import Definitions.Def_DecDynMatch_Supplement_Feasible

namespace DecDynMatch.Supplement

open DecDynMatch

universe u

/-- **Theorem 2 (Cumulative Mismatch of Π_g).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic
Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), Theorem 2, p.9: "∀ K ≥ 2,
feasible function g, dynamic matching instance I and time horizon T > H, the decentralized matching
protocol Π_g satisfies D_{Π_g}(T; I) = O(g(t*) + K² N_g(T))." (eq. (7)); p.8: "Given g, we define a
deterministic decentralized matching protocol Π_g by replacing L in Equation (4) and Algorithm 1
with L ← F_g(a − ℓ)."

For every feasible `g` there is a constant `C` (depending only on `g`) such that for every number of
arms `K`, every finite player type `ι`, every instance `I` and every horizon `T > H`, the mismatch
count of SC-DA with replay rule `F_g` is at most `C (g(t*) + K² N_g(T))`.

**Formalization Note.** `Π_g` is the base execution with replay rule `Fg K g`, so `D_{Π_g}(T; I)` is
the base `D (Fg K g) I T`; `N_g(T)` is the base `Ng K g T` (`s₀ = H`). The constant is chosen after
`g` and before `K`, `I`, `T` (App. A.5, p.21: "a constant depending only on g"; eq. (32)). The final
market may be empty. `Feasible` drops polynomial-time computability. -/
theorem theorem_2 :
    ∀ g : ℕ → ℕ, Feasible g → ∃ C : ℝ, ∀ (K : ℕ) (ι : Type u) [Fintype ι] (I : Instance K ι)
      (T : ℕ), H K < T →
        (D (Fg K g) I T : ℝ) ≤ C * ((g (tstar I) : ℝ) + (K : ℝ) ^ 2 * (Ng K g T : ℝ)) := by sorry

end DecDynMatch.Supplement
