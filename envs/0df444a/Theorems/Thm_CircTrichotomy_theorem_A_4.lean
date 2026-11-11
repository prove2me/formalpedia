-- Prove2me | Theorems.Thm_CircTrichotomy_theorem_A_4
-- name    : CircTrichotomy.theorem_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:12.126787+00:00
-- url     : https://prove2.me/theorems/8e3981cb-8b63-4e9d-b0e5-55eb2c5a985c
-- title:
--   Theorem A.4 — reductions preserve $O(f)$ and $\Omega(f)$ for mild $f$ [GM26b]
-- statement:
--   **Theorem A.4** ([GM26b, Theorem 3.7]). Let $f$ be a mild function, and let $L_1\subseteq\Sigma_1^+$ and $L_2\subseteq\Sigma_2^+$ be languages over finite non-empty alphabets with $L_1\le L_2$. Then
--   1. if $c(L_2)\in O(f)$, then $c(L_1)\in O(f)$;
--   2. if $c(L_1)\in\Omega(f)$, then $c(L_2)\in\Omega(f)$,
--
--   with the Hardy–Littlewood $\Omega$. The languages need not be regular.
--
--   The theorem transfers circuit lower bounds along rational truth-table reductions. Proved in [GM26b] (arXiv:2609.18484).
--
--   Differences from the source:
--   - encoding: n-circuits (G, ≺, λ, out) of Definition A.2 → Circuit α n m: non-input gates numbered in topological order, each with a non-empty list of wire sources (input labels (i, Γ) and earlier gates); outputs are the gates read by no gate, in bijection with Fin m; reason: every finite DAG has a topological numbering; one input gate per label (duplicate input gates change no value, size or depth); size and depth as in Definition A.2
--   - encoding: functions ℕ>0 → ℝ≥0 (c(L), sizes, depths) → functions ℕ → ℝ; c(L)(0) = 0 and family size/depth 0 at n = 0; reason: O, o and Hardy–Littlewood Ω only look at all but finitely many, resp. infinitely many n, so the value at n = 0 is never seen
--   - encoding: languages L₁ ⊆ Σ₁⁺, L₂ ⊆ Σ₂⁺ over finite alphabets → [] ∉ L₁, [] ∉ L₂, Fintype and Nonempty for both alphabets; reason: p.18 states the languages are positive; Definition A.2 takes non-empty alphabets
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem A.4, p.19

import Mathlib
import Definitions.Def_CircTrichotomy_circuitComplexity
import Definitions.Def_CircTrichotomy_BigO
import Definitions.Def_CircTrichotomy_HLOmega
import Definitions.Def_CircTrichotomy_Reduces
import Definitions.Def_CircTrichotomy_IsMild

set_option autoImplicit false

namespace CircTrichotomy

/-- **Theorem A.4 ([GM26b, Theorem 3.7])** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem A.4, p.19; cited from Göller, Manuel,
arXiv:2609.18484): "Let f : ℕ>0 → ℝ≥0 be a mild function. Let L₁ and L₂ be languages such that
L₁ ≤ L₂.
(1) If c(L₂) ∈ O(f), then c(L₁) ∈ O(f).
(2) If c(L₁) ∈ Ω(f), then c(L₂) ∈ Ω(f)."

`L₁` and `L₂` are languages over two finite non-empty alphabets `β` and `α`; they need not be
regular. Both clauses are stated.

**Formalization Note** `Ω` is the Hardy–Littlewood `HLOmega`. Languages are positive (`[] ∉ L₁`,
`[] ∉ L₂`, p.16 and p.18: "Let L₁ ⊆ Σ₁⁺ and L₂ ⊆ Σ₂⁺ be languages"). -/
theorem theorem_A_4 {β α : Type} [Fintype β] [Nonempty β] [Fintype α] [Nonempty α]
    (f : ℕ → ℝ) (hf : IsMild f) (L₁ : Language β) (L₂ : Language α) (h₁ : [] ∉ L₁) (h₂ : [] ∉ L₂)
    (hred : Reduces L₁ L₂) :
    (BigO (fun n => (circuitComplexity L₂ n : ℝ)) f →
        BigO (fun n => (circuitComplexity L₁ n : ℝ)) f) ∧
      (HLOmega (fun n => (circuitComplexity L₁ n : ℝ)) f →
        HLOmega (fun n => (circuitComplexity L₂ n : ℝ)) f) := by sorry

end CircTrichotomy
