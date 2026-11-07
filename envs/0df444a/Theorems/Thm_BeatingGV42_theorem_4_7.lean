-- Prove2me | Theorems.Thm_BeatingGV42_theorem_4_7
-- name    : BeatingGV42.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:14.767203+00:00
-- url     : https://prove2.me/theorems/ecfd1c57-7570-459d-bd20-09a92dac86ae
-- title:
--   Theorem 4.7 — generalized Drinfeld–Vlăduţ bound $\sum_r r\beta_r/(Q^{r/2}-1)\le1$ [Tsfasman; TV02, Thm 3.2]
-- statement:
--   Let $(F_i/\mathbb F_Q)_{i\ge1}$ be an asymptotically exact sequence of function fields, with limits $\beta_r=\lim_i B_r(F_i)/g_i$. Then
--   $$
--   \sum_{r=1}^{\infty}\frac{r\beta_r}{Q^{r/2}-1}\le 1 .
--   \tag{4.12}
--   $$
--   This is a cited result (Tsfasman 1992, in the formulation of Tsfasman–Vlăduţ 2002, Theorem 3.2). In the proof of Lemma 4.8 it forces $\beta_r=0$ for $r>1$ along asymptotically optimal sequences.
--
--   **Formalization Note** `Fs : ℕ → FunctionFieldOver k`, $Q$ = `Nat.card k`, and `IsAsympExact Fs β` gives the limits. The series is stated through its partial sums; its terms are nonnegative ($\beta_r\ge0$ as a limit of nonnegative ratios, $Q^{r/2}>1$), so this is the same as the series bound. $Q^{r/2}$ is a real power.
--
--   Differences from the source:
--   - encoding: a sequence (F_i/F_Q)^∞_{i=1} of function fields with genera g_i → ∞ → Fs : ℕ → FunctionFieldOver k (indexed from 0), each Fs i a field with [IsCurveOver k], [Algebra.EssFiniteType k] and ConstantsAreBase k whose carrier lies in the universe of k, F_Q a finite field k with Q = Nat.card k; g_i → ∞ is the first conjunct of IsAsympOptimal / IsAsympExact; reason: index shift and bundling only, with the platform encoding of a function field of one variable with full constant field (as in claim_4_2); a function field over a finite field is countable, so it has a copy in every universe; the §4.3 standing assumption is kept
--   - encoding: Σ_{r=1}^∞ rβ_r/(Q^{r/2} − 1) ≤ 1 → ∀ R, Σ_{r ∈ Icc 1 R} r β r/(Q^{r/2} − 1) ≤ 1; reason: the terms are nonnegative, so the series is ≤ 1 exactly when every partial sum is
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Theorem 4.7, p.17 (PDF p.19), cited from [TV02, Theorem 3.2]

import Mathlib
import Definitions.Def_BeatingGV42_IsAsympExact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace BeatingGV42

/-- **Theorem 4.7** (generalized Drinfeld–Vlăduţ bound, [Tsf92], in the formulation of
[TV02, Theorem 3.2]; Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.3, p.17 (PDF p.19)): "Let (F_i/F_Q)^∞_{i=1} be an asymptotically exact
sequence of function fields. Then Σ_{r=1}^∞ rβ_r/(Q^{r/2} − 1) ≤ 1." (4.12)

**Formalization Note** A sequence `(F_i/F_Q)_{i ≥ 1}` is `Fs : ℕ → FunctionFieldOver k` (indexed from `0`), each
`Fs i` a function field of one variable over the finite field `k` with full constant field, and
`Q = Nat.card k`. `g_i = genusFF k (Fs i).carrier`, `B_r(F_i) = numPlaces k (Fs i).carrier r`,
`N_i = B_1(F_i)`; the §4.3 standing assumption `g_i → ∞` is part of `IsAsympOptimal`/`IsAsympExact`. The limits `β_r = lim B_r(F_i)/g_i` are the function `β` of
`IsAsympExact Fs β`. The series is stated through its partial sums: every `β_r ≥ 0` (a limit of
nonnegative ratios) and `Q^{r/2} − 1 > 0`, so the terms are nonnegative and "the series is `≤ 1`" is
"every partial sum is `≤ 1`". `Q^{r/2}` is a real power. -/
theorem theorem_4_7 {k : Type u} [Field k] [Finite k] (Fs : ℕ → FunctionFieldOver k)
    (β : ℕ → ℝ) (hFs : IsAsympExact Fs β) (R : ℕ) :
    ∑ r ∈ Finset.Icc 1 R, (r : ℝ) * β r / ((Nat.card k : ℝ) ^ ((r : ℝ) / 2) - 1) ≤ 1 := by sorry

end BeatingGV42
