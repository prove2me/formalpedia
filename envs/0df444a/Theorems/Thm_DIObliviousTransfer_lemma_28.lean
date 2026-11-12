-- Prove2me | Theorems.Thm_DIObliviousTransfer_lemma_28
-- name    : DIObliviousTransfer.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:04:37.858708+00:00
-- url     : https://prove2.me/theorems/c026bd2b-9176-456e-b027-d7b6ecedb4a8
-- title:
--   Lemma 28 — conservative residual guessing bound
-- statement:
--   Consider a one-copy Magic Square strategy with even-row and odd-column outputs and average loss $\varepsilon$ over independent uniform questions. Fix questions $x,y$ and an index $k\ne y$. After producing his column, Dave guesses Charlie's entry $A^{\mathrm{in}}[k]$ from his retained quantum memory and the revealed $x$. His success probability is at most
--   $$\tfrac12+15\sqrt\varepsilon.$$
--
--   This is the one-copy input to the selector-aware repetition theorem.
--
--   Differences from the source:
--
--   - encoding: quantum systems and strategies in the abstract (registers, measurements, instruments) → finite-dimensional registers, matrices over finite types, POVMs and Kraus instruments; reason: Decision D2: registers are polynomial-size or finite-alphabet throughout; same instances
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 28, p.63 (PDF p.65)

import Mathlib
import Definitions.Def_DIObliviousTransfer_MS

namespace DIObliviousTransfer

/-- **Lemma 28 (Conservative residual guessing bound)**, Batra, Chen, Jain, Zhang,
arXiv:2610.01421 (held version, sha256 8334c039…), p.63 (PDF p.65). For a one-copy Magic Square
strategy with even-row and odd-column outputs and average loss `ε` over independent uniform
questions, for fixed questions `x, y` and `k ≠ y`, Dave's probability of guessing Charlie's entry
`A^in[k]` after producing his column, from his retained quantum memory and the revealed `x`, is
at most `1/2 + 15√ε`.

**Formalization Note** (decision D2). The strategy is finite-dimensional (`MSStrategy`); Dave's
guess is any two-outcome POVM on his post-instrument space, chosen after his column outcome and
knowing `x, y`. The guessing probability is the probability of a correct guess given `x, y`. -/
theorem lemma_28 (S : MSStrategy) (x y k : Fin 3) (hk : k ≠ y)
    (N : Bool × Bool → Bool → Matrix S.HD' S.HD' ℂ) (hN : ∀ b, IsPOVM (N b)) :
    S.guessProb x y k N ≤ 1 / 2 + 15 * Real.sqrt S.avgLoss := by sorry

end DIObliviousTransfer
