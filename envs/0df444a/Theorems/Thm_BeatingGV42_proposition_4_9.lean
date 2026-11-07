-- Prove2me | Theorems.Thm_BeatingGV42_proposition_4_9
-- name    : BeatingGV42.proposition_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:41.849294+00:00
-- url     : https://prove2.me/theorems/7512eefe-4cbe-4acc-8d61-be977f3d144e
-- title:
--   Proposition 4.9 — $\Psi_{a,q}(t,\delta)<0$ gives $q$-ary codes of relative distance $\delta$ and rate $\ge R(a,q)$
-- statement:
--   Let $Q$ be a square prime power, $q$ an integer with $2\le q\le Q$, and $a\in\bigl(\frac2{\sqrt Q-1},1\bigr)$; put $\delta_0=1-a$. Suppose there are $\delta\in(\delta_0,1-1/q)$ and $t\in(0,1/Q)$ with $\Psi_{a,q}(t,\delta)<0$. Then there is a family $\{C_i\}_{i\ge1}$ of $q$-ary codes of lengths $n_i\to\infty$, with asymptotic relative distance at least $\delta$ and asymptotic rate at least
--   $$
--   R(a,q)=1-\left(1+\frac1{\sqrt Q-1}-a\right)\frac{\ln Q}{\ln q}.
--   $$
--   This is the general sufficient condition; Theorem 1.1 is its instance $Q=49$, $q=42$ with the parameters chosen in §4.5.
--
--   **Formalization Note** $Q,q$ are natural numbers with `IsPrimePow Q` and `IsSquare Q`; the family is `HasCodeFamily q δ (rateR Q q a)`: lengths $\to\infty$, every code of minimum distance $\ge\delta n_i$, and $\liminf$ rate $\ge R(a,q)$ in $\varepsilon$-form.
--
--   Differences from the source:
--   - encoding: Suppose there exist δ ∈ (δ_0, 1 − 1/q) and t ∈ (0, 1/Q) such that Ψ_{a,q}(t, δ) < 0 → δ t : ℝ given as arguments with the hypotheses; reason: the conclusion is then stated for that δ, exactly as in the proof
--   - reading: asymptotic relative distance δ → relative distance at least δ; reason: the proof shows d(C_2^{(i)}) ≥ ⌈δN_i⌉ ≥ δN_i (4.20) and Theorem 1.1 uses 'at least δ'
--   - generalization: asymptotic relative distance (at least) δ: liminf d(C_i)/n_i ≥ δ → every code C_i has minimum distance ≥ δ n_i; reason: pointwise implies the liminf form; it is what the proof delivers (4.20)
--   - encoding: asymptotic rate at least R(a, q) → ∀ ε > 0, eventually R(a, q) − ε ≤ log_q |C_i| / n_i; reason: equivalent to liminf ≥ R(a, q); avoids Filter.liminf junk
--   - encoding: a family {C_i}^∞_{i=1} of q-ary codes of lengths n_i → ∞ → n : ℕ → ℕ with Tendsto n atTop atTop and C i : Finset (Fin (n i) → Fin q) for every i : ℕ; reason: any alphabet of size q is in bijection with Fin q, and the family the proof builds for i > i_0 is re-indexed from 0
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Proposition 4.9, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_BeatingGV42_HasCodeFamily
import Definitions.Def_BeatingGV42_Psi
import Definitions.Def_BeatingGV42_rateR

set_option autoImplicit false

namespace BeatingGV42

/-- **Proposition 4.9** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.4, p.20 (PDF p.22)): "Suppose there exist δ ∈ (δ_0, 1 − 1/q) and
t ∈ (0, 1/Q) such that Ψ_{a,q}(t, δ) < 0. Then there exists a family {C_i}^∞_{i=1} of q-ary codes of
lengths n_i → ∞, with asymptotic relative distance δ and asymptotic rate at least
R(a, q) := 1 − (1 + 1/(√Q − 1) − a) ln Q/ln q."
Standing assumptions of §4.4 (p.20): "let Q be a square prime power, let q be an integer satisfying
2 ≤ q ≤ Q, and let a ∈ (2/(√Q − 1), 1)"; `δ_0 = 1 − a`.

**Formalization Note** `Q, q : ℕ` with `IsPrimePow Q`, `IsSquare Q`, `2 ≤ q ≤ Q`. "Suppose there
exist δ, t" is taken as `δ`, `t` given with their hypotheses. "Asymptotic relative distance δ" is
read as "at least δ", which is what the proof shows (eq. (4.20)), and the family is a
`HasCodeFamily q δ (rateR Q q a)`: lengths `→ ∞`, every code of minimum distance `≥ δ n_i`, and
`liminf` rate `≥ R(a, q)`. -/
theorem proposition_4_9 (Q q : ℕ) (hQ : IsPrimePow Q) (hQsq : IsSquare Q) (hq : 2 ≤ q)
    (hqQ : q ≤ Q) (a : ℝ) (ha : 2 / (Real.sqrt Q - 1) < a) (ha1 : a < 1) (δ t : ℝ)
    (hδ : 1 - a < δ) (hδ' : δ < 1 - 1 / (q : ℝ)) (ht : 0 < t) (ht' : t < 1 / (Q : ℝ))
    (hΨ : Psi Q q a t δ < 0) :
    HasCodeFamily q δ (rateR Q q a) := by sorry

end BeatingGV42
