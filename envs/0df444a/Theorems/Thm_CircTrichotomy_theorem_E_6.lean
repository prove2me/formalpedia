-- Prove2me | Theorems.Thm_CircTrichotomy_theorem_E_6
-- name    : CircTrichotomy.theorem_E_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:00:29.658539+00:00
-- url     : https://prove2.me/theorems/59e0460e-4304-40e8-9cd1-1f44550c3829
-- title:
--   Theorem E.6 — $\mathrm{Occ}_t$ in size $O(\log^2 n)$ and depth $O(1)$
-- statement:
--   **Theorem E.6.** For every fixed $t\ge1$, $\mathrm{Occ}_t$ is computable by a circuit family of size $O(\log^2 n)$ and depth $O(1)$: there are $n$-circuits $C_n$ over $\{0,1\}$ with $t\lceil\log_2(n+1)\rceil$ outputs that, on every $w\in\{0,1\}^n$ with exactly $t$ ones, output the binary representations (least significant bit first) of the positions of the ones in increasing order, with $|C_n|\in O(\log^2 n)$ and $\mathrm{depth}(C_n)\in O(1)$.
--
--   It is the circuit primitive behind the implication (9) ⇒ (1) of Theorem 2.8.
--
--   Differences from the source:
--   - encoding: n-circuits (G, ≺, λ, out) of Definition A.2 → Circuit α n m: non-input gates numbered in topological order, each with a non-empty list of wire sources (input labels (i, Γ) and earlier gates); outputs are the gates read by no gate, in bijection with Fin m; reason: every finite DAG has a topological numbering; one input gate per label (duplicate input gates change no value, size or depth); size and depth as in Definition A.2
--   - encoding: functions ℕ>0 → ℝ≥0 (c(L), sizes, depths) → functions ℕ → ℝ; c(L)(0) = 0 and family size/depth 0 at n = 0; reason: O, o and Hardy–Littlewood Ω only look at all but finitely many, resp. infinitely many n, so the value at n = 0 is never seen
--   - encoding: log → Real.logb 2; reason: log is base two (p.58); every asymptotic class used is invariant under the base
--   - encoding: ℓ = ⌈log(n + 1)⌉ and outputs bin_ℓ(p₀), …, bin_ℓ(p_{t−1}) → Nat.clog 2 (n + 1) and output j·ℓ + b = bit b of p_j; reason: Nat.clog 2 (n + 1) is the least ℓ with n + 1 ≤ 2^ℓ; f_C concatenates the outputs in order (Definition A.2)
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem E.6, p.59

import Mathlib
import Definitions.Def_CircTrichotomy_OccComputable

set_option autoImplicit false

namespace CircTrichotomy

/-- **Theorem E.6** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem E.6, p.59): "Occ_t is computable by a circuit family of size
O(log² n) and depth O(1)." (For each fixed t ∈ ℕ>0, p.59.)

**Formalization Note** `log` is `Real.logb 2` (p.58: "log denotes the base two logarithm"). -/
theorem theorem_E_6 (t : ℕ) (ht : 0 < t) :
    OccComputable t (fun n => Real.logb 2 n ^ 2) (fun _ => 1) := by sorry

end CircTrichotomy
