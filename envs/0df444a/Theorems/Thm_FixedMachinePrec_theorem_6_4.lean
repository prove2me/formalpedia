-- Prove2me | Theorems.Thm_FixedMachinePrec_theorem_6_4
-- name    : FixedMachinePrec.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:51.077438+00:00
-- url     : https://prove2.me/theorems/b14685a0-15ee-4c8c-bce2-cb66e1c77cec
-- title:
--   Theorem 6.4 — RAM operation count $O(L)+m^{O(m^2)}n^{E(m)}$ and $O(L)+m^{O(m^2)}n^{E(m)}\log n$
-- statement:
--   Put $E(m)=6m^2+13m+1$. There are RAM programs $P_{\mathrm{dl}}$, $P_{\mathrm{opt}}$ and one constant $c$ such that for every $m\ge3$, every acyclic instance $G$ with distinct arcs, and every word size $W\ge c\,m^2(\lfloor\log_2(mn)\rfloor+1)$:
--
--   1. for every deadline $T$, $P_{\mathrm{dl}}$ outputs exactly the answer of Algorithm 6 (NO, or the reconstructed schedule) within
--   $$c\,L_T+m^{c m^2}n^{E(m)}$$
--   elementary operations, where $L_T$ is the length of the input with the deadline;
--   2. $P_{\mathrm{opt}}$ outputs exactly the optimum schedule constructed by Algorithm 7 within
--   $$c\,L+m^{c m^2}n^{E(m)}\lfloor\log_2n\rfloor\quad\text{and within}\quad c\,L+m^{c m^2}n^{11m^2}$$
--   elementary operations.
--
--   **Formalization Note** $O(L)+m^{O(m^2)}f$ is $c\,L+m^{cm^2}f$ with one $c$ for all $m$. The programs implement the Lean functions `deadline` and `optimum`, with all deterministic choices fixed.
--
--   Differences from the source:
--   - encoding: O(L) + m^{O(m²)} f → c·L + m^{c·m²}·f for one constant c chosen before m; reason: the paper's uniformity: “all constants … specified as functions of its input”
--   - reading: words of O(m² log(N + 2)) bits suffice (p.20), N ≤ mn → correct at every word size W ≥ c·m²·(⌊log₂(mn)⌋ + 1); reason: N ≤ mn and, when padding is used, N ≥ max(m, n), so the two thresholds agree up to a constant
--   - encoding: the RAM of Section 6 reading input of length L → RAMInstr: the TrulySubcubicAPSP instruction set with a bitwise input tape and an output tape, unit cost per instruction; reason: reading the input once costs O(L); a preloaded input could not be addressed when the deadline is long
--   - encoding: log n → ⌊log₂ n⌋ (Nat.log2); reason: equal up to a factor 2 for n ≥ 2; for n ≤ 1 the source's proof gives O(L + 1)
--   - encoding: deadline feasibility and reconstruction of a schedule → the program outputs the encoding of the value of the Lean function deadline (Algorithm 6); reason: the operation count is for the paper's algorithm
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Theorem 6.4, pp.23–24

import Mathlib
import Definitions.Def_FixedMachinePrec_Deadline
import Definitions.Def_FixedMachinePrec_Encoding
import Definitions.Def_FixedMachinePrec_RAM

namespace FixedMachinePrec

/-- **Theorem 6.4 (Overall operation count).** Jansen, *Precedence Constraint Scheduling on a Fixed
Number of Machines* (manuscript, sha256 08cdf3e1…), Theorem 6.4, pp.23–24: "Put
E(m) = 6m² + 13m + 1. With K_node = 4m + 5 and K_cut = m + 3, deadline feasibility and
reconstruction of a schedule use O(L) + m^{O(m²)} n^{E(m)} RAM operations. Optimization, including
construction of an optimum schedule, uses O(L) + m^{O(m²)} n^{E(m)} log n. In particular, for every
m ≥ 3 the latter is at most O(L) + m^{O(m²)} n^{11m²}."

There are RAM programs `Pdl`, `Popt` and one constant `c` such that for every `m ≥ 3` and every
acyclic instance with distinct arcs, at every word size `W ≥ c·m²·(⌊log₂(mn)⌋ + 1)`:
1. for every deadline `T`, `Pdl` outputs exactly the encoding of the answer of Algorithm 6,
   `Deadline(G, m, T)`, within `c·L_T + m^{c·m²}·n^{E(m)}` operations;
2. `Popt` outputs exactly the encoding of the schedule returned by Algorithm 7, `Optimum(G, m)`,
   within `c·L + m^{c·m²}·n^{E(m)}·⌊log₂ n⌋` and within `c·L + m^{c·m²}·n^{11m²}` operations.

**Formalization Note** The programs implement the paper's Algorithms 6 and 7 with every
deterministic choice fixed as in the Lean functions `deadline` and `optimum`. `O(L) + m^{O(m²)} f`
is `c·L + m^{c·m²}·f` for one constant `c` chosen before `m`; the word-size clause reads "words of
O(m² log(N + 2)) bits suffice" (p.20) with the padded size `N ≤ mn`. The statement covers every `n` (the proof treats `n ≤ 1`
in `O(L + 1)` time). -/
theorem theorem_6_4 :
    ∃ (Pdl Popt : List RAMInstr) (c : ℕ),
      ∀ m : ℕ, 3 ≤ m → ∀ G : Instance, G.Acyclic → G.arcs.Nodup →
        ∀ W : ℕ, c * m ^ 2 * (Nat.log2 (m * G.n) + 1) ≤ W →
          (∀ T : ℕ, ∃ t : ℕ,
            RAMOutputs W Pdl (encDeadlineInput m G T) (encDeadlineResult (deadline G m T)) t ∧
            t ≤ c * (encDeadlineInput m G T).length +
              m ^ (c * m ^ 2) * G.n ^ (6 * m ^ 2 + 13 * m + 1)) ∧
          (∃ t : ℕ, RAMOutputs W Popt (encInput m G) (encSchedule (optimum G m).2) t ∧
            t ≤ c * (encInput m G).length +
              m ^ (c * m ^ 2) * G.n ^ (6 * m ^ 2 + 13 * m + 1) * Nat.log2 G.n ∧
            t ≤ c * (encInput m G).length + m ^ (c * m ^ 2) * G.n ^ (11 * m ^ 2)) := by sorry

end FixedMachinePrec
