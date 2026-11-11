-- Prove2me | Theorems.Thm_CircTrichotomy_fact_A_5
-- name    : CircTrichotomy.fact_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:00:26.655521+00:00
-- url     : https://prove2.me/theorems/47cf9c45-1b62-4c47-b23d-a36a6f3e342b
-- title:
--   Fact A.5 — regular languages are in $\mathrm{SizeDepth}(O(n),O(\log n))$
-- statement:
--   **Fact A.5.** Let $\Sigma$ be a finite non-empty alphabet and $L\subseteq\Sigma^+$ a regular language. Then
--   $$L\in\mathrm{SizeDepth}\bigl(O(n),\,O(\log n)\bigr),$$
--   that is, some family of single-output circuits $(C_n)_{n\ge1}$ computes $L$ with $|C_n|\in O(n)$ and $\mathrm{depth}(C_n)\in O(\log n)$.
--
--   This supplies the upper bound $c(L)\in O(n)$ of the linear case of the trichotomy.
--
--   Differences from the source:
--   - encoding: a regular language L ⊆ Σ⁺ over a finite non-empty alphabet Σ → Language.IsRegular L (Mathlib: accepted by a finite automaton), [] ∉ L, Fintype α, Nonempty α; reason: p.17 identifies regular, recognizable by a finite semigroup, and accepted by a finite automaton; L ⊆ Σ⁺ is [] ∉ L
--   - encoding: n-circuits (G, ≺, λ, out) of Definition A.2 → Circuit α n m: non-input gates numbered in topological order, each with a non-empty list of wire sources (input labels (i, Γ) and earlier gates); outputs are the gates read by no gate, in bijection with Fin m; reason: every finite DAG has a topological numbering; one input gate per label (duplicate input gates change no value, size or depth); size and depth as in Definition A.2
--   - encoding: functions ℕ>0 → ℝ≥0 (c(L), sizes, depths) → functions ℕ → ℝ; c(L)(0) = 0 and family size/depth 0 at n = 0; reason: O, o and Hardy–Littlewood Ω only look at all but finitely many, resp. infinitely many n, so the value at n = 0 is never seen
--   - encoding: log → Real.logb 2; reason: log is base two (p.58); every asymptotic class used is invariant under the base
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Fact A.5, p.19

import Mathlib
import Definitions.Def_CircTrichotomy_InSizeDepth
import Definitions.Def_CircTrichotomy_BigO

set_option autoImplicit false

namespace CircTrichotomy

/-- **Fact A.5** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Fact A.5, p.19): "For each regular language L we have
L ∈ SizeDepth(O(n), O(log n))."

Every regular `L ⊆ α⁺` over a finite non-empty alphabet is computed by a family of single-output
circuits of size `O(n)` and depth `O(log n)`.

**Formalization Note** `log` is `Real.logb 2`. Languages are positive (`[] ∉ L`, p.16). -/
theorem fact_A_5 {α : Type} [Fintype α] [Nonempty α] (L : Language α) (hreg : L.IsRegular)
    (hL : [] ∉ L) :
    InSizeDepth L (fun f => BigO f (fun n => (n : ℝ))) (fun g => BigO g (fun n => Real.logb 2 n)) := by sorry

end CircTrichotomy
