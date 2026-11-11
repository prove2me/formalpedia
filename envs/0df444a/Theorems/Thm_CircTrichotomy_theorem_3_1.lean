-- Prove2me | Theorems.Thm_CircTrichotomy_theorem_3_1
-- name    : CircTrichotomy.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:47.611983+00:00
-- url     : https://prove2.me/theorems/4ab7889f-d121-4212-97b7-7e6333d90675
-- title:
--   Theorem 3.1 — outside $\mathbf X$ the circuit complexity is $\Omega(n)$
-- statement:
--   **Theorem 3.1.** Let $\Sigma$ be a finite non-empty alphabet and $L\subseteq\Sigma^+$ a regular language. If the syntactic morphism $\eta_L$ is not in $\mathbf X$, then
--   $$c(L)\in\Omega(n),$$
--   with the Hardy–Littlewood $\Omega$: there is $c>0$ with $c(L)(n)\ge c\,n$ for infinitely many $n$.
--
--   This is the direction (3) ⇒ (4) of Theorem 2.8 and the lower bound of the linear case of the trichotomy.
--
--   Differences from the source:
--   - encoding: a regular language L ⊆ Σ⁺ over a finite non-empty alphabet Σ → Language.IsRegular L (Mathlib: accepted by a finite automaton), [] ∉ L, Fintype α, Nonempty α; reason: p.17 identifies regular, recognizable by a finite semigroup, and accepted by a finite automaton; L ⊆ Σ⁺ is [] ∉ L
--   - encoding: n-circuits (G, ≺, λ, out) of Definition A.2 → Circuit α n m: non-input gates numbered in topological order, each with a non-empty list of wire sources (input labels (i, Γ) and earlier gates); outputs are the gates read by no gate, in bijection with Fin m; reason: every finite DAG has a topological numbering; one input gate per label (duplicate input gates change no value, size or depth); size and depth as in Definition A.2
--   - encoding: functions ℕ>0 → ℝ≥0 (c(L), sizes, depths) → functions ℕ → ℝ; c(L)(0) = 0 and family size/depth 0 at n = 0; reason: O, o and Hardy–Littlewood Ω only look at all but finitely many, resp. infinitely many n, so the value at n = 0 is never seen
--   - encoding: the ω-powers in the identities (1) of X → any e, f with IsOmegaPow (idempotent positive powers); reason: in a finite semigroup (S(L) for regular L, S for a stamp) there is exactly one such element, the ω-power
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 3.1, p.6 (restated p.43)

import Mathlib
import Definitions.Def_CircTrichotomy_circuitComplexity
import Definitions.Def_CircTrichotomy_HLOmega
import Definitions.Def_CircTrichotomy_syntMorphism
import Definitions.Def_CircTrichotomy_InX

set_option autoImplicit false

namespace CircTrichotomy

/-- **Theorem 3.1** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 3.1, p.6; restated p.43): "Let L be a regular language. If η_L
is not in X, then c(L) ∈ Ω(n)."

**Formalization Note** `Ω` is the Hardy–Littlewood `HLOmega` (Definition A.1). Languages are
positive (`[] ∉ L`, p.16: "Unless stated otherwise we will be working with positive languages"). -/
theorem theorem_3_1 {α : Type} [Fintype α] [Nonempty α] (L : Language α) (hreg : L.IsRegular)
    (hL : [] ∉ L) (hX : ¬ InX (syntMorphism L)) :
    HLOmega (fun n => (circuitComplexity L n : ℝ)) (fun n => (n : ℝ)) := by sorry

end CircTrichotomy
