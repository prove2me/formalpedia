-- Prove2me | Theorems.Thm_BeatingGV42_claim_4_10
-- name    : BeatingGV42.claim_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:29.016425+00:00
-- url     : https://prove2.me/theorems/56cf1d82-b27c-458d-9ae8-efb22b9aac8e
-- title:
--   Claim 4.10 — for large $i$, $\mathbb E_\gamma[W_q(C^{(i)}_\gamma,\lceil\delta N_i\rceil)]\le1$
-- statement:
--   Let $Q$ be a square prime power, $2\le q\le Q$, $a\in\bigl(\frac2{\sqrt Q-1},1\bigr)$, $\delta\in(1-a,1-1/q)$ and $t\in(0,1/Q)$ with $\Psi_{a,q}(t,\delta)<0$. Let $(F_i/\mathbb F_Q)_{i\ge1}$ be an asymptotically optimal sequence, $N_i$ the number of rational places of $F_i$, $D_i$ the sum of **all** rational places of $F_i$, $m_i=\lfloor aN_i\rfloor$, $d_i=\lceil\delta N_i\rceil$, and for $\gamma\in\mathcal C^{m_i}_{F_i}$ let $C^{(i)}_\gamma=C_L(D_i,G_\gamma)$ with representatives $G_\gamma$ whose supports avoid $D_i$. Then for all sufficiently large $i$,
--   $$
--   \mathbb E_\gamma\Bigl[W_q\bigl(C^{(i)}_\gamma,d_i\bigr)\Bigr]\le 1,
--   $$
--   the expectation being over $\gamma\in\mathcal C^{m_i}_{F_i}$ uniformly at random. Consequently some $C^{(i)}_\gamma$ has $W_q\le1$, and Lemma 4.1 applies to it.
--
--   **Formalization Note** `Fs : ℕ → FunctionFieldOver k`; for each $i$, `P i : Fin N_i → Place` enumerates the rational places (injective, degree $1$, every degree-$1$ place attained). The representatives `G i` are any choice with $[G_i\gamma]=\gamma$ and supports avoiding the $P_{i,j}$ (they exist by Claim 4.2). $m_i$ is an integer floor, $d_i$ a natural ceiling; $\mathbb E_\gamma=\frac1{h_{F_i}}\sum_{\gamma\in\mathcal C^{m_i}_{F_i}}$.
--
--   Differences from the source:
--   - encoding: a sequence (F_i/F_Q)^∞_{i=1} of function fields with genera g_i → ∞ → Fs : ℕ → FunctionFieldOver k (indexed from 0), each Fs i a field with [IsCurveOver k], [Algebra.EssFiniteType k] and ConstantsAreBase k whose carrier lies in the universe of k, F_Q a finite field k with Q = Nat.card k; g_i → ∞ is the first conjunct of IsAsympOptimal / IsAsympExact; reason: index shift and bundling only, with the platform encoding of a function field of one variable with full constant field (as in claim_4_2); a function field over a finite field is countable, so it has a copy in every universe; the §4.3 standing assumption is kept
--   - reading: D = P_1 + ⋯ + P_{N_i} is the sum of its rational places → P i : Fin (numPlaces 1) → Place injective, of degree 1, hitting every degree-1 place; reason: an enumeration of all rational places; same divisor D
--   - encoding: for each class γ ∈ C^m_F fix a representative G_γ as in Claim 4.2 → any G : Pic k F → Divisor k F with [G γ] = γ and ∀ i, G γ (P i) = 0 for every γ ∈ C^m_F; reason: the statement holds for each choice of representatives, which is what fixing an arbitrary one means
--   - encoding: E_γ, expectation over γ ∈ C^m_F chosen uniformly at random → (∑ᶠ γ ∈ degClasses k F m, ·) / classNumber k F; reason: the first display of the proof of Lemma 4.3 (p.14) writes E_γ as (1/h_F)·Σ_{γ∈C^m_F}, using |C^m_F| = h_F (p.11, p.13)
--   - encoding: m_i = ⌊aN_i⌋, d_i = ⌈δN_i⌉ → Int.floor (a * N_i), Nat.ceil (δ * N_i); reason: δ > 1 − a > 0, so the natural ceiling is the integer ceiling
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Claim 4.10, p.21 (PDF p.23), in the setting of the proof of Proposition 4.9, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_BeatingGV42_IsAsympOptimal
import Definitions.Def_BeatingGV42_classNumber
import Definitions.Def_BeatingGV42_degClasses
import Definitions.Def_BeatingGV42_goppaCode
import Definitions.Def_BeatingGV42_truncWE
import Definitions.Def_BeatingGV42_Psi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter AlgebraicCurve

universe u

namespace BeatingGV42

/-- **Claim 4.10** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.4, p.21 (PDF p.23)): in the proof of Proposition 4.9, with an
asymptotically optimal sequence `(F_i/F_Q)`, `m_i = ⌊aN_i⌋`, `D = P_1 + ⋯ + P_{N_i}` the sum of the
rational places of `F_i`, the codes `C^{(i)}_γ = C_L(D, G_γ)` for `γ ∈ C^{m_i}_{F_i}`, and
"d_i := ⌈δN_i⌉": "For all i sufficiently large, we have E_γ [W_q(C^{(i)}_γ, d_i)] ≤ 1, where the
expectation is taken over γ ∈ C^{m_i}_{F_i} chosen uniformly at random."
Hypotheses: the §4.4 standing ones (p.20: `Q` a square prime power, `2 ≤ q ≤ Q`,
`a ∈ (2/(√Q − 1), 1)`) and those of Proposition 4.9 (`δ ∈ (1 − a, 1 − 1/q)`, `t ∈ (0, 1/Q)`,
`Ψ_{a,q}(t, δ) < 0`).

**Formalization Note** A sequence `(F_i/F_Q)_{i ≥ 1}` is `Fs : ℕ → FunctionFieldOver k` (indexed from `0`), each
`Fs i` a function field of one variable over the finite field `k` with full constant field, and
`Q = Nat.card k`. `g_i = genusFF k (Fs i).carrier`, `B_r(F_i) = numPlaces k (Fs i).carrier r`,
`N_i = B_1(F_i)`; the §4.3 standing assumption `g_i → ∞` is part of `IsAsympOptimal`/`IsAsympExact`. For each `i`, `P i : Fin N_i → Place` enumerates **all** rational
places of `F_i` (injective, every value of degree 1, every degree-1 place attained). The
representatives `G i γ` are any choice with `[G i γ] = γ` and `supp(G i γ) ∩ supp(D) = ∅` on
`C^{m_i}_{F_i}` (they exist by Claim 4.2). `m_i = ⌊a N_i⌋` (an integer floor), `d_i = ⌈δ N_i⌉` (a natural
ceiling; `δ > 0`), and `E_γ = (1/h_{F_i}) Σ_{γ ∈ C^{m_i}_{F_i}}` as in Lemma 4.3. -/
theorem claim_4_10 {k : Type u} [Field k] [Finite k] (hQ : IsSquare (Nat.card k))
    (q : ℕ) (hq : 2 ≤ q) (hqQ : q ≤ Nat.card k)
    (a : ℝ) (ha : 2 / (Real.sqrt (Nat.card k : ℝ) - 1) < a) (ha1 : a < 1)
    (δ t : ℝ) (hδ : 1 - a < δ) (hδ' : δ < 1 - 1 / (q : ℝ))
    (ht : 0 < t) (ht' : t < 1 / (Nat.card k : ℝ)) (hΨ : Psi (Nat.card k) q a t δ < 0)
    (Fs : ℕ → FunctionFieldOver k) (hFs : IsAsympOptimal Fs)
    (P : ∀ i, Fin (numPlaces k (Fs i).carrier 1) → Place k (Fs i).carrier)
    (hP : ∀ i, Function.Injective (P i)) (hdeg : ∀ i j, (P i j).deg = 1)
    (hall : ∀ i, ∀ v : Place k (Fs i).carrier, v.deg = 1 → ∃ j, P i j = v)
    (G : ∀ i, Pic k (Fs i).carrier → Divisor k (Fs i).carrier)
    (hG : ∀ i, ∀ γ ∈ degClasses k (Fs i).carrier ⌊a * (numPlaces k (Fs i).carrier 1 : ℝ)⌋,
      (QuotientAddGroup.mk (G i γ) : Pic k (Fs i).carrier) = γ ∧ ∀ j, G i γ (P i j) = 0) :
    ∀ᶠ i in atTop,
      (∑ᶠ γ ∈ degClasses k (Fs i).carrier ⌊a * (numPlaces k (Fs i).carrier 1 : ℝ)⌋,
          truncWE q (goppaCode (P i) (G i γ)) ⌈δ * (numPlaces k (Fs i).carrier 1 : ℝ)⌉₊) /
        (classNumber k (Fs i).carrier : ℝ) ≤ 1 := by sorry

end BeatingGV42
