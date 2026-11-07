-- Prove2me | Theorems.Thm_DynHaussler_lemma_32
-- name    : DynHaussler.lemma_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:12.175798+00:00
-- url     : https://prove2.me/theorems/feb41a83-8e51-4cb5-9f3e-a74d3c037ea2
-- title:
--   Lemma 32 — finite-horizon determinization of a perfect-information game
-- statement:
--   Consider a game of $T$ rounds between an adversary and a constructor. In each round the adversary first chooses an input from a nonempty set, and the constructor then chooses an action from a nonempty set; the legal choices may depend on the preceding moves. Both players observe all earlier moves, and the constructor also observes the current input. Each terminal history is designated winning or losing for the constructor.
--
--   If against every deterministic adversary strategy some deterministic constructor strategy wins, then there is one deterministic constructor strategy that wins against every adversary strategy.
--
--   The source's hypothesis, that one randomized constructor strategy wins with positive probability against every deterministic adversary strategy, implies the hypothesis above. The lemma turns the randomized sampling-and-routing protocol of Proposition 2 into a deterministic family of causal experts.
--
--   **Formalization Note** Inputs and actions are arbitrary types; legal sets are nonempty at every legal history before the end; strategies are legal when they choose legal moves at every legal history.
--
--   Differences from the source:
--   - generalization: one randomized constructor strategy wins with positive probability against every deterministic adversary strategy → for every legal deterministic adversary strategy there is a legal deterministic constructor strategy whose play wins; reason: a winning realization of the randomized strategy against α gives such a deterministic strategy, so the source's hypothesis implies this one; it also avoids measure theory on arbitrary action sets
--   - encoding: wins against every adversary strategy → wins against every legal deterministic adversary strategy; reason: every play against a randomized adversary is a play against one of its deterministic realizations
--   - encoding: inputs, actions and legal sets depending on the preceding moves → types I, A and sets legalI t h, legalA t h i indexed by the history h : Fin t → I × A; reason: same games
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 32, p.43 (PDF p.45); proof pp.43–44

import Mathlib
import Definitions.Def_DynHaussler_IsLegalHist
import Definitions.Def_DynHaussler_gamePlay

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 32 (Finite-horizon determinization).** Consider a game of `T` rounds between an adversary
and a constructor. In each round the adversary first chooses an input from a nonempty set, and the
constructor then chooses an action from a nonempty set. The legal choices may depend on the
preceding moves. Both players observe all earlier moves, and the constructor also observes the
current input. Each terminal history is designated winning or losing for the constructor. If one
randomized constructor strategy wins with positive probability against every deterministic
adversary strategy, then there is a deterministic constructor strategy that wins against every
adversary strategy.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 32, p.43 (PDF p.45).

**Formalization Note** Inputs and actions are arbitrary types `I`, `A`; the legal sets
`legalI t h`, `legalA t h i` depend on the history `h` of the `t` preceding rounds (and on the
current input), and are nonempty at every legal history (`IsLegalHist`) before the end of the game.
A deterministic adversary strategy `α` maps each history to an input, a deterministic constructor
strategy `κ` maps each history and current input to an action; a strategy is legal if it chooses
legal moves at every legal history. `gamePlay α κ T` is the terminal history, and `win` designates
the winning terminal histories. The hypothesis is that against every legal deterministic adversary
strategy some legal deterministic constructor strategy wins; a randomized constructor strategy
winning with positive probability against `α` has a winning realization, whose actions along the
play form such a strategy, so the paper's hypothesis implies this one. Winning against every
deterministic adversary strategy is winning against every adversary strategy, since each play
against a randomized adversary is a play against one of its realizations. -/
theorem lemma_32 {I A : Type*} (T : ℕ) (legalI : (t : ℕ) → (Fin t → I × A) → Set I)
    (legalA : (t : ℕ) → (Fin t → I × A) → I → Set A)
    (hI : ∀ t < T, ∀ h : Fin t → I × A, IsLegalHist legalI legalA h → (legalI t h).Nonempty)
    (hA : ∀ t < T, ∀ h : Fin t → I × A, IsLegalHist legalI legalA h →
      ∀ i ∈ legalI t h, (legalA t h i).Nonempty)
    (win : (Fin T → I × A) → Prop)
    (hwin : ∀ α : (t : ℕ) → (Fin t → I × A) → I,
      (∀ t < T, ∀ h : Fin t → I × A, IsLegalHist legalI legalA h → α t h ∈ legalI t h) →
      ∃ κ : (t : ℕ) → (Fin t → I × A) → I → A,
        (∀ t < T, ∀ h : Fin t → I × A, IsLegalHist legalI legalA h →
          ∀ i ∈ legalI t h, κ t h i ∈ legalA t h i) ∧
        win (gamePlay α κ T)) :
    ∃ κ : (t : ℕ) → (Fin t → I × A) → I → A,
      (∀ t < T, ∀ h : Fin t → I × A, IsLegalHist legalI legalA h →
        ∀ i ∈ legalI t h, κ t h i ∈ legalA t h i) ∧
      ∀ α : (t : ℕ) → (Fin t → I × A) → I,
        (∀ t < T, ∀ h : Fin t → I × A, IsLegalHist legalI legalA h → α t h ∈ legalI t h) →
        win (gamePlay α κ T) := by sorry

end DynHaussler
