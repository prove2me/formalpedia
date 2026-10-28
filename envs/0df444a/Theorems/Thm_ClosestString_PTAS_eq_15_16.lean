-- Prove2me | Theorems.Thm_ClosestString_PTAS_eq_15_16
-- name    : ClosestString.PTAS.eq_15_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:19:05.924023+00:00
-- url     : https://prove2.me/theorems/f626051f-9c82-4674-b5e1-244a83beeffc
-- title:
--   (15)–(16) and the final chain — d(s′, t′_i) ≤ (1 + 1/(2r−1) + 3εr)·d_opt
-- statement:
--   Let $s,f$ be strings of length $L$, $t_1,\dots,t_n$ and $t'_1,\dots,t'_n$ strings of length $L$, $d\ge0$ an integer with $d(s,t_i)\le d$ for every $i$, $Q$ a set of positions with complement $P$, $r\ge1$ and $\varepsilon\ge0$. Let $s^*$ be $s$ on $P$ and $f$ on $Q$. Assume
--
--   1. (Fact 1) $d^Q(t_l,f)-d^Q(t_l,s)\le d/(2r-1)$ for every $l$;
--   2. $|P|\le r\,d$;
--   3. (Fact 2) $d(s^*,t'_i)\le d(s^*,t_i)+2\varepsilon|P|$ for every $i$;
--   4. $x$ solves problem (8) for $(t',P,d^Q(t'_i,f))$ within error $\varepsilon|P|$: $d(t'_i|_P,x)+d(t'_i|_Q,f|_Q)\le d_0+\varepsilon|P|$ for every $i$, where $d_0=\min_x\max_i\big(d(t'_i|_P,x)+d(t'_i|_Q,f|_Q)\big)$.
--
--   Then the string $s'$ with $s'|_P=x$ and $s'|_Q=f|_Q$ satisfies, for every $i$,
--
--   $$d(s',t'_i)\ \le\ \Big(1+\frac1{2r-1}+3\varepsilon r\Big)d.$$
--
--   In the paper $s$ is an optimal center, $d=d_{\mathrm{opt}}$ and $f=t_{i_1}$; the chain passes through (15), $d(s^*,t'_i)\le(1+\frac1{2r-1}+2\varepsilon r)d_{\mathrm{opt}}$, and (16). It is the deterministic core of Theorem 9.
--
--   Differences from the source:
--
--   - reading: (15)–(16) are steps of the proof of Theorem 9 that combine Fact 1, |P| ≤ r d_opt, Fact 2 and the solver's error → a deterministic implication whose premises are those four facts; reason: the paper proves the premises separately (Lemma 1, proof of Theorem 7, Fact 2, Lemma 6); the chain is the step that combines them
--   - generalization: Fact 1: |{j ∈ Q | t_{i1}[j] ≠ t_l[j] and t_{i1}[j] ≠ s[j]}| ≤ d_opt/(2r−1) → d^Q(t_l, f) − d^Q(t_l, s) ≤ d/(2r−1); reason: the paper's Fact 1 implies this form, which is the one (15) uses ("d(s∗, ti) = d^P(s, ti) + d^Q(ti1, ti) ≤ d(s, ti) + d_opt/(2r−1)")
--   - generalization: s optimal, t_i, t′_i substrings of s_i, f = t_{i1}, r ≥ 2, ε > 0 → arbitrary strings, any radius bound d, r ≥ 1, ε ≥ 0; reason: the chain uses only the four premises; the paper's setting is a special case
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 11, eq. (15) and p. 12, eq. (16) and the final chain of the proof of Theorem 9

import Mathlib
import Definitions.Def_ClosestString_PTAS_Algorithm

namespace ClosestString.PTAS

/-- **(15)–(16) and the final chain** (proof of Theorem 9, Li, Ma & Wang, arXiv:cs/0002012v1,
pp. 11–12), deterministic, for arbitrary strings of length `L`: let `s` be a center with
`d(s, t_i) ≤ d` for all `i`, `f` (the paper's `t_{i1}`) a string, `Q` a position set with
complement `P`, `r ≥ 1`, `ε ≥ 0`, and assume Fact 1 (`d^Q(t_l, f) − d^Q(t_l, s) ≤ d/(2r−1)`),
`|P| ≤ r d`, and Fact 2's event `d(s∗, t′_i) ≤ d(s∗, t_i) + 2ε|P|` with `s∗ = s` on `P`, `f` on `Q`.
If `x` solves problem (8) for `(t′, P, d^Q(t′_i, f))` within error `ε|P|`, then
`s′ = x` on `P`, `f` on `Q` satisfies `d(s′, t′_i) ≤ (1 + 1/(2r−1) + 3εr) d` for every `i`. -/
theorem eq_15_16 {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {n L : ℕ}
    (s f : Fin L → A) (t t' : Fin n → Fin L → A) (d : ℕ) (hd : ∀ i, hammingDist s (t i) ≤ d)
    (Q : Finset (Fin L)) (r : ℕ) (hr : 1 ≤ r)
    (hFact1 : ∀ l, (distOn Q (t l) f : ℝ) - distOn Q (t l) s ≤ d / (2 * (r : ℝ) - 1))
    (hP : Qᶜ.card ≤ r * d) (ε : ℝ) (hε : 0 ≤ ε)
    (hFact2 : ∀ i, (hammingDist (splice Qᶜ s f) (t' i) : ℝ)
      ≤ hammingDist (splice Qᶜ s f) (t i) + 2 * ε * Qᶜ.card)
    (x : Fin L → A)
    (hx : ∀ i, (distOn Qᶜ (t' i) x : ℝ) + distOn Q (t' i) f
      ≤ opt8 t' Qᶜ (fun i => distOn Q (t' i) f) + ε * Qᶜ.card) :
    ∀ i, (hammingDist (splice Qᶜ x f) (t' i) : ℝ)
      ≤ (1 + 1 / (2 * (r : ℝ) - 1) + 3 * ε * r) * d := by sorry

end ClosestString.PTAS
