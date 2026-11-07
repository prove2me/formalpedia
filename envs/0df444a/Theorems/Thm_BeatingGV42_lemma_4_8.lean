-- Prove2me | Theorems.Thm_BeatingGV42_lemma_4_8
-- name    : BeatingGV42.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:15.78907+00:00
-- url     : https://prove2.me/theorems/7453918f-d207-4cf8-a39b-03b88aa35236
-- title:
--   Lemma 4.8 — $\ln h_{F_i}/N_i\to\kappa$ and $\ln Z_{F_i}(t)/N_i\to-\ln(1-t)$ along optimal sequences
-- statement:
--   Let $(F_i/\mathbb F_Q)_{i\ge1}$ be an asymptotically optimal sequence of function fields, with $N_i$ rational places and class numbers $h_{F_i}$. Then
--   $$
--   \lim_{i\to\infty}\frac{\ln h_{F_i}}{N_i}=\frac{\ln Q}{\sqrt Q-1}-\ln(1-1/Q),
--   \tag{4.13}
--   $$
--   and for every $0<t<1/Q$,
--   $$
--   \lim_{i\to\infty}\frac{\ln Z_{F_i}(t)}{N_i}=-\ln(1-t).
--   \tag{4.14}
--   $$
--   These two limits turn the bound of Corollary 4.5 into the exponent $\Psi_{a,q}$ of §4.4.
--
--   **Formalization Note** `Fs : ℕ → FunctionFieldOver k`, $Q$ = `Nat.card k`; $h_{F_i}$ = `classNumber`, $Z_{F_i}(t)$ = `zetaAt` (a `tsum`), $N_i$ = `numPlaces … 1`. Both limits are stated, as one conjunction. Divisions by $N_i$ are real; $N_i\to\infty$, so the junk value at $N_i=0$ affects finitely many terms.
--
--   Differences from the source:
--   - encoding: a sequence (F_i/F_Q)^∞_{i=1} of function fields with genera g_i → ∞ → Fs : ℕ → FunctionFieldOver k (indexed from 0), each Fs i a field with [IsCurveOver k], [Algebra.EssFiniteType k] and ConstantsAreBase k whose carrier lies in the universe of k, F_Q a finite field k with Q = Nat.card k; g_i → ∞ is the first conjunct of IsAsympOptimal / IsAsympExact; reason: index shift and bundling only, with the platform encoding of a function field of one variable with full constant field (as in claim_4_2); a function field over a finite field is countable, so it has a copy in every universe; the §4.3 standing assumption is kept
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Lemma 4.8, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_BeatingGV42_IsAsympOptimal
import Definitions.Def_BeatingGV42_classNumber
import Definitions.Def_BeatingGV42_zeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter Topology

universe u

namespace BeatingGV42

/-- **Lemma 4.8** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.3, p.17 (PDF p.19)): "Let (F_i/F_Q)^∞_{i=1} be an asymptotically optimal
sequence of function fields. Then lim_{i→∞} ln h_{F_i}/N_i = ln Q/(√Q − 1) − ln(1 − 1/Q), (4.13)
and for every 0 < t < 1/Q, lim_{i→∞} ln Z_{F_i}(t)/N_i = −ln(1 − t). (4.14)"
Both limits are stated, as one conjunction.

**Formalization Note** A sequence `(F_i/F_Q)_{i ≥ 1}` is `Fs : ℕ → FunctionFieldOver k` (indexed from `0`), each
`Fs i` a function field of one variable over the finite field `k` with full constant field, and
`Q = Nat.card k`. `g_i = genusFF k (Fs i).carrier`, `B_r(F_i) = numPlaces k (Fs i).carrier r`,
`N_i = B_1(F_i)`; the §4.3 standing assumption `g_i → ∞` is part of `IsAsympOptimal`/`IsAsympExact`. `h_{F_i} = classNumber`, `Z_{F_i}(t) = zetaAt` (a `tsum`, convergent for
`0 < t < 1/Q`). The quotients by `N_i` are real divisions; `N_i → ∞` along an asymptotically optimal
sequence, so the junk value at `N_i = 0` affects at most finitely many terms. -/
theorem lemma_4_8 {k : Type u} [Field k] [Finite k] (Fs : ℕ → FunctionFieldOver k)
    (hFs : IsAsympOptimal Fs) :
    Tendsto (fun i => Real.log (classNumber k (Fs i).carrier : ℝ) /
        (numPlaces k (Fs i).carrier 1 : ℝ)) atTop
      (𝓝 (Real.log (Nat.card k : ℝ) / (Real.sqrt (Nat.card k : ℝ) - 1) -
        Real.log (1 - 1 / (Nat.card k : ℝ)))) ∧
    ∀ t : ℝ, 0 < t → t < 1 / (Nat.card k : ℝ) →
      Tendsto (fun i => Real.log (zetaAt k (Fs i).carrier t) / (numPlaces k (Fs i).carrier 1 : ℝ))
        atTop (𝓝 (-Real.log (1 - t))) := by sorry

end BeatingGV42
