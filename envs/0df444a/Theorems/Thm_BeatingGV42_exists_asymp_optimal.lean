-- Prove2me | Theorems.Thm_BeatingGV42_exists_asymp_optimal
-- name    : BeatingGV42.exists_asymp_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:26.614885+00:00
-- url     : https://prove2.me/theorems/a1da7bdf-ef9b-42f9-acf7-77ac0d324859
-- title:
--   Garcia–Stichtenoth [GS95]: asymptotically optimal sequences of function fields exist over $\mathbb F_Q$, $Q$ a square
-- statement:
--   Let $\mathbb F_Q$ be a finite field whose size $Q$ is a square. Then there is an asymptotically optimal sequence $(F_i/\mathbb F_Q)_{i\ge1}$ of function fields over $\mathbb F_Q$: genera $g_i\to\infty$ and $N_i/g_i\to\sqrt Q-1$.
--
--   This is the cited input with which the proof of Proposition 4.9 opens ("Take an asymptotically optimal sequence … such as the one obtained from the Garcia–Stichtenoth tower [GS95]"); everything else in §4.4 is proved in the paper.
--
--   **Formalization Note** `k` is any finite field with `IsSquare (Nat.card k)`; the sequence is `Fs : ℕ → FunctionFieldOver k`, with function fields in the universe of `k`.
--
--   Differences from the source:
--   - reading: Take an asymptotically optimal sequence (F_i/F_Q)^∞_{i=1} of function fields over F_Q, such as the one obtained from the Garcia-Stichtenoth tower [GS95] (Q a square prime power, §4.4) → ∀ finite field k with IsSquare (Nat.card k), ∃ Fs : ℕ → FunctionFieldOver k, IsAsympOptimal Fs; reason: the sentence uses the existence of such a sequence for every square prime power Q, which is what [GS95] provides
--   - encoding: a sequence (F_i/F_Q)^∞_{i=1} of function fields with genera g_i → ∞ → Fs : ℕ → FunctionFieldOver k (indexed from 0), each Fs i a field with [IsCurveOver k], [Algebra.EssFiniteType k] and ConstantsAreBase k whose carrier lies in the universe of k, F_Q a finite field k with Q = Nat.card k; g_i → ∞ is the first conjunct of IsAsympOptimal / IsAsympExact; reason: index shift and bundling only, with the platform encoding of a function field of one variable with full constant field (as in claim_4_2); a function field over a finite field is countable, so it has a copy in every universe; the §4.3 standing assumption is kept
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), proof of Proposition 4.9, p.20 (PDF p.22), citing Garcia–Stichtenoth [GS95]

import Mathlib
import Definitions.Def_BeatingGV42_IsAsympOptimal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace BeatingGV42

/-- **Existence of asymptotically optimal sequences over `F_Q`, `Q` a square** (Garcia–Stichtenoth
[GS95]; Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), proof of Proposition 4.9, p.20 (PDF p.22): "Take an asymptotically optimal sequence
(F_i/F_Q)^∞_{i=1} of function fields over F_Q, such as the one obtained from the Garcia-Stichtenoth
tower [GS95].") The proof of Proposition 4.9 rests on this cited input; §4.4 assumes `Q` is a square
prime power.

**Formalization Note** `F_Q` is any finite field `k` whose cardinality `Q = Nat.card k` is a perfect
square (it is automatically a prime power). The sequence is `Fs : ℕ → FunctionFieldOver k`, with
function fields in the universe of `k`; `IsAsympOptimal` includes `g_i → ∞`. -/
theorem exists_asymp_optimal (k : Type u) [Field k] [Finite k] (hQ : IsSquare (Nat.card k)) :
    ∃ Fs : ℕ → FunctionFieldOver k, IsAsympOptimal Fs := by sorry

end BeatingGV42
