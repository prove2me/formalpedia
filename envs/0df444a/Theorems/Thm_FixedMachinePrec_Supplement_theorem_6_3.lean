-- Prove2me | Theorems.Thm_FixedMachinePrec_Supplement_theorem_6_3
-- name    : FixedMachinePrec.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:58:42.120845+00:00
-- url     : https://prove2.me/theorems/6bdf0624-3ee7-45a6-9492-2f75f64e97d9
-- title:
--   Theorem 6.3 — the explicit evaluator uses $O(\mathrm{poly}(m)\,B_{\mathrm{node}}B_{\mathrm{cut}}^2(N+2)^{2m+1})$ RAM operations
-- statement:
--   Let $J=\{1,\dots,N\}$ carry a strict partial order $\prec$ (irreflexive and transitive), and let $\mathcal F,\mathcal F_{\mathrm{cut}}$ be arbitrary families of subsets of $J$ with $B_{\mathrm{node}}=|\mathcal F|\ge1$ and $B_{\mathrm{cut}}=|\mathcal F_{\mathrm{cut}}|\ge1$, supplied without repetition as $N$-bit incidence vectors together with the $N\times N$ matrix of $\prec$.
--
--   There are one RAM program $P$ and absolute constants $c,k$ such that for every $m\ge3$, every $N\ge m$, all such $\prec,\mathcal F,\mathcal F_{\mathrm{cut}}$ (listed in any order), and every word size
--   $$W\ \ge\ c\big(\lfloor\log_2(B_{\mathrm{node}}B_{\mathrm{cut}}(N+2)^{2m+1})\rfloor+1\big),$$
--   the program $P$ halts on the evaluator input word within
--   $$c\,m^k\,B_{\mathrm{node}}\,B_{\mathrm{cut}}^2\,(N+2)^{2m+1}$$
--   elementary RAM operations, with exactly the evaluator output word on its output tape: the values $a(X)$ that Algorithms 2–5 (EvaluateFamily) compute for all rows $X\in\mathcal F$ and the stored schedules $\sigma(X)$ of all accepted sets.
--
--   The count includes building the dictionary of $\mathcal F$ from the raw incidence vectors and copying the stored schedules. It is the per-call cost used in the overall operation count of Theorem 6.4, where $\mathcal F=\mathcal F_{4m+5}$ and $\mathcal F_{\mathrm{cut}}=\mathcal F_{m+3}$.
--
--   **Formalization Note** The RAM is the mission's published unit-cost word RAM (`RAMInstr`, `RAMOutputs`), with a bitwise input tape and an output tape. $\mathrm{poly}(m)$ is $m^k$ and the $O$-constant is $c$, both chosen before $m$, $N$ and the families, so the one program is uniform in $m$. The time bound has no additive input-length term, as printed.
--
--   Differences from the source:
--   - encoding: O(poly(m) B_node B_cut² (N+2)^{2m+1}) → c·m^k·B_node·B_cut²·(N+2)^{2m+1} with absolute c, k chosen before m, N and the families; reason: poly(m) is a fixed polynomial, bounded by a constant times a fixed power of m
--   - generalization: words large enough to hold the working addresses and counters (p.20) → correct at every word size W ≥ c·(⌊log₂(B_node·B_cut·(N+2)^{2m+1})⌋ + 1); reason: the paper fixes no word size for arbitrary families; addresses of the stored states and schedules need Θ of this many bits, and requiring every larger W as well specializes to the source's machine
--   - encoding: the RAM of Section 6 → RAMInstr: the published instruction set with a bitwise input tape and an output tape, unit cost per instruction; reason: the same model as the mission's Theorem 6.4; reading the input once is within the bound
--   - encoding: Algorithms 2–5 use … RAM operations, including … the stored schedules of all accepted sets → the program outputs exactly the encoding of evaluateFamily's table on the rows of F (a(X) and σ(X)), in the order of Algorithm 4; reason: the operation count is for the paper's algorithm and its stored schedules
--   - encoding: distinct family members supplied as N-bit incidence vectors → every duplicate-free list lF, lCut with F = lF.toFinset, F_cut = lCut.toFinset, bit j of a vector = (j ∈ X); reason: the paper fixes no order of supply; quantifying over every order covers every supply
--   - encoding: job labels 1, …, N → Fin N (0-based); reason: Lean convention, the shift preserves all orders
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Theorem 6.3, p.22 (proof pp.22–23); RAM model §6, p.20

import Mathlib
import Definitions.Def_FixedMachinePrec_FullSchedule
import Definitions.Def_FixedMachinePrec_RAM
import Definitions.Def_FixedMachinePrec_Supplement_EvalEncoding

namespace FixedMachinePrec.Supplement

open FixedMachinePrec

/-- **Theorem 6.3 (Cost of the explicit evaluator).** Jansen, *Precedence Constraint Scheduling on
a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Theorem 6.3, p.22: "Let B_node = |F| ≥ 1
and B_cut = |F_cut| ≥ 1, with the distinct family members supplied as N-bit incidence vectors and
the global transitive order precomputed. For m ≥ 3 and N ≥ m, Algorithms 2–5 use
O(poly(m) B_node B_cut² (N + 2)^{2m+1}) RAM operations, including exact dictionary construction and
the stored schedules of all accepted sets."

There are one RAM program `P` and constants `c, k`, chosen before everything else, such that for
all `m ≥ 3`, `N ≥ m`, every strict partial order `prec` on `Fin N`, every duplicate-free listing
`lF`, `lCut` of nonempty families `F`, `F_cut` of subsets of `Fin N`, and every word size
`W ≥ c·(⌊log₂(B_node·B_cut·(N+2)^{2m+1})⌋ + 1)`, the program run on the evaluator input word halts
within `c·m^k·B_node·B_cut²·(N+2)^{2m+1}` operations with exactly the evaluator output word of
`evaluateFamily prec m F F_cut` on its output tape.

**Formalization Note** `poly(m)` is `m^k` and the `O` constant is `c`, both absolute. `m`, `N`
and the families are read from the input, so the one program covers every `m`. The time bound has
no additive input-length term, as in the paper (the input has length `O(N² + (B_node + B_cut)N)`).
The word size is the paper's "words large enough to hold the working addresses and counters"
(p.20), read for arbitrary families as `Θ(log(B_node·B_cut·(N+2)^{2m+1}))` bits; the statement
holds at every larger word size too. -/
theorem theorem_6_3 :
    ∃ (P : List RAMInstr) (c k : ℕ),
      ∀ m N : ℕ, 3 ≤ m → m ≤ N →
      ∀ (prec : Fin N → Fin N → Prop) [DecidableRel prec], IsStrictOrder' prec →
      ∀ lF lCut : List (Finset (Fin N)), lF.Nodup → lCut.Nodup →
        1 ≤ lF.length → 1 ≤ lCut.length →
      ∀ W : ℕ, c * (Nat.log2 (lF.length * lCut.length * (N + 2) ^ (2 * m + 1)) + 1) ≤ W →
        ∃ t : ℕ,
          RAMOutputs W P (encEvalInput m N prec lF lCut)
            (encEvalOutput m prec lF.toFinset lCut.toFinset) t ∧
          t ≤ c * m ^ k * lF.length * lCut.length ^ 2 * (N + 2) ^ (2 * m + 1) := by sorry

end FixedMachinePrec.Supplement
