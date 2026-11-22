-- Prove2me | Theorems.Thm_AvgPHETH_Supplement_theorem_7_1
-- name    : AvgPHETH.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:01:54.459613+00:00
-- url     : https://prove2.me/theorems/ca340fbe-4aaf-4116-8bfe-4ffd837eda4d
-- title:
--   Theorem 7.1 — enhanced depth hierarchy theorem: agreement on critical assignments
-- statement:
--   For every $k\ge1$ there exist $C_k,w_0\in\mathbb N$ and a family of AND-rooted layered alternating formulas $F_{k,w}$ of depth $k$ on $\mathrm{poly}(w)$ input bits such that the following holds for every $w\ge w_0$:
--
--   1. all internal fan-ins of $F_{k,w}$ are at most $w^{C_k}$;
--   2. for every $t\le w/4$, no OR-rooted alternating circuit $C$ with depth $k+1$, bottom width at most $t$, and at most $2^t$ gates above the bottom layer agrees with $F_{k,w}$ on all critical assignments. That is, some critical assignment $\alpha$ of $F_{k,w}$ has $C(\alpha)\ne F_{k,w}(\alpha)$.
--
--   The lower bound holds against circuits that are only required to agree with the hard formula on its critical assignments. This is what lets the formulas be embedded into the selector trees of the oracle construction in Section 8.
--
--   Differences from the source:
--   - reading: for every $k\in\mathbb N$ → for every $k\ge1$; reason: an AND-rooted formula has a root gate, so its depth is at least $1$; the paper's $\mathbb N$ starts at $1$ (Section 8 restates "for all $k\ge1$" as "for all $k\in\mathbb N$"), and the proof's induction starts at $k=1$
--   - encoding: on $\mathrm{poly}(w)$ input bits → $F_{k,w}$ has $N(w)\le p(w)$ variables for one polynomial $p$ and every $w$; the circuit is over the same variables; reason: the usual meaning of $\mathrm{poly}(w)$
--   - encoding: a gate's inputs, with repeated use allowed → a nonempty set of vertices of the previous layer; reason: a repeated wire changes neither an AND nor an OR gate, and removing it increases no fan-in or count; fan-in starts at one on p.16
--   - reading: $t\le w/4$ → natural $t$ with $4t\le w$; reason: $t$ bounds a bottom width (a fan-in) and is an integer throughout §7 (the induction applies the projection switching lemma with width $t$); for natural $t$ the two conditions coincide
--   - reading: layered alternating formula (leaves labelled by literals or constants) → every gate of $F_{k,w}$ has at least one child (Formula.IsLayeredAlt); reason: leaves are the literal/constant nodes, so a childless gate would end a root-to-leaf path at a gate; the condition only restricts the family the theorem asserts to exist, so the Lean statement is at least as strong
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 7.1, p.30 (PDF 32); definitions of §4.3, pp.16–17 (PDF 18–19)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Formula_IsLayeredAlt
import Definitions.Def_AvgPHETH_Supplement_Formula_FanInLe
import Definitions.Def_AvgPHETH_Supplement_Formula_IsCritical
import Definitions.Def_AvgPHETH_Supplement_AltCircuit_eval

namespace AvgPHETH.Supplement

/-- **Theorem 7.1** (enhanced depth hierarchy theorem, Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.30 (PDF 32)): for every `k ≥ 1`
there exist `C_k, w₀ ∈ ℕ` and a family of AND-rooted alternating formulas `F_{k,w}` of depth `k` on
`poly(w)` input bits such that, for every `w ≥ w₀`, all internal fan-ins of `F_{k,w}` are at most
`w^{C_k}`, and, for every `t ≤ w/4`, no OR-rooted alternating circuit with depth `k + 1`, bottom width
at most `t`, and at most `2^t` gates above the bottom layer agrees with `F_{k,w}` on all critical
assignments.

**Formalization Note** `F_{k,w}` has `N w ≤ p(w)` variables for one polynomial `p`; the circuit is
over the same variables. Bottom width is the largest fan-in in gate layer `1`; the gates above the
bottom layer are those in layers `2, …, k+1`. "Does not agree on all critical assignments" is: some
critical assignment of `F_{k,w}` gets different values. `k ∈ ℕ` is read as `k ≥ 1` (an AND-rooted
formula has depth at least `1`). -/
theorem theorem_7_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (Ck w₀ : ℕ) (p : Polynomial ℕ) (N : ℕ → ℕ) (F : (w : ℕ) → Formula (Fin (N w))),
      (∀ w, N w ≤ p.eval w) ∧ (∀ w, (F w).IsLayeredAlt true k) ∧
      ∀ w, w₀ ≤ w →
        (F w).FanInLe (w ^ Ck) ∧
        ∀ t : ℕ, 4 * t ≤ w → ∀ C : AltCircuit (Fin (N w)),
          C.depth = k + 1 → C.outAnd = false →
          (∀ g : Fin (C.size 1), (C.wires 0 g).card ≤ t) →
          ∑ j ∈ Finset.Icc 2 C.depth, C.size j ≤ 2 ^ t →
          ∃ α : Fin (N w) → Bool, (F w).IsCritical α ∧ C.eval α ≠ (F w).eval α := by sorry

end AvgPHETH.Supplement
