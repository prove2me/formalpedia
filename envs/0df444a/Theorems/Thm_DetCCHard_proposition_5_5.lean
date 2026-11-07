-- Prove2me | Theorems.Thm_DetCCHard_proposition_5_5
-- name    : DetCCHard.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:51.728111+00:00
-- url     : https://prove2.me/theorems/c3eb575b-10c5-499f-acba-f17d337ce6cf
-- title:
--   Proposition 5.5 — iterating an amplifier with (i)–(iii) from $R_0$: YES cost $\le B_i$, NO cost $= B_i + i$
-- statement:
--   Fix a threshold $\rho = 2^{-L}$ ($L \ge 1$), an overhead $h$, a source promise (YES or NO), and a round map $R \mapsto R^+$ on weighted tables with the properties of Theorem 5.3:
--
--   1. on either promise $D(R^+) \le D(R) + h + 1$, and on YES $D(R^+) \le D(R) + h$;
--   2. on NO, if $D(R) = d \ge 3$ and $\mathcal P(R; \rho, d)$, then $D(R^+) = d + h + 1$ and $\mathcal P(R^+; \rho, d + h + 1)$;
--   3. on either promise $\operatorname{rank}(R^+) \le 2^h \operatorname{rank}(R)$.
--
--   Iterate it from the matrix $R_0$ of Lemma 5.4 with this $L$, and let $R_i$ be the matrix after $i \ge 0$ rounds. Put $B_i = d_0 + ih$, $H_i = B_i + i$ and $r_i = 2^{B_i - 1}$. A YES graph gives $D(R_i) \le B_i$. A NO graph gives $D(R_i) = H_i$ and $\mathcal P(R_i; \rho, H_i)$. On either promise $\operatorname{rank}(R_i) \le r_i$ and $D(R_i) \le H_i$.
--
--   After $k$ rounds the YES and NO costs differ by $k$ bits, which is the additive gap of Theorem 1.1.
--
--   **Formalization Note** The promises are propositions with "YES or NO" as a hypothesis; $d_0 = \log p_0 + 1$ with $p_0 = \mathrm{pow2}(64(L+1))$.
--
--   Differences from the source:
--   - generalization: the round map of Theorem 5.3 (one case, fixed source graph) → every map on weighted tables with properties (i)–(iii) of Theorem 5.3; reason: the paper's round map is one such map
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Proposition 5.5, p.18, with Theorem 5.3 (i)–(iii), p.17

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_DetCCHard_pow2
import Definitions.Def_DetCCHard_WMat

namespace DetCCHard

/-- **Proposition 5.5 (Iterated amplification)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held
version sha256 ad552d13…a4a03, Proposition 5.5, p.18, with Theorem 5.3 (i)–(iii), p.17). Fix a
round map `R ↦ R⁺` with threshold `ρ = 2^{-L}` and overhead `h` satisfying, for a source graph
that is YES or NO:
(i) on either promise `D(R⁺) ≤ D(R) + h + 1`, and on YES `D(R⁺) ≤ D(R) + h`;
(ii) on NO, if `D(R) = d ≥ 3` and `P(R; ρ, d)`, then `D(R⁺) = d + h + 1` and `P(R⁺; ρ, d + h + 1)`;
(iii) on either promise `rank(R⁺) ≤ 2^h rank(R)`.
Iterate it from the matrix `R₀` of Lemma 5.4 with this `L`, and let `R_i` be the matrix after
`i ≥ 0` rounds. Put `B_i = d₀ + ih`, `H_i = B_i + i` and `r_i = 2^{B_i − 1}`. A YES graph gives
`D(R_i) ≤ B_i`. A NO graph gives `D(R_i) = H_i` and `P(R_i; ρ, H_i)`. On either promise
`rank(R_i) ≤ r_i` and `D(R_i) ≤ H_i`.

**Formalization Note** The promises are propositions `yes`, `no` with `yes ∨ no`; the round map is
any map on weighted tables with properties (i)–(iii) (the paper's construction of Theorem 5.3 is
one such map, so it is a special case). `d₀ = log p₀ + 1` with `p₀ = pow2(64(L + 1))`, rank over
`ℝ`. -/
theorem proposition_5_5 (L : ℕ) (hL : 1 ≤ L) (h : ℕ) (yes no : Prop) (hprom : yes ∨ no)
    (round : WMat → WMat)
    (h1 : ∀ R : WMat, Dcost (round R).entry ≤ Dcost R.entry + h + 1)
    (h1y : yes → ∀ R : WMat, Dcost (round R).entry ≤ Dcost R.entry + h)
    (h2 : no → ∀ (R : WMat) (d : ℕ), Dcost R.entry = d → 3 ≤ d →
      DeletionBounds R.entry R.μX R.μY (1 / 2 ^ L) d →
      Dcost (round R).entry = d + h + 1 ∧
        DeletionBounds (round R).entry (round R).μX (round R).μY (1 / 2 ^ L) ((d + h + 1 : ℕ) : ℤ))
    (h3 : ∀ R : WMat, realRank (round R).entry ≤ 2 ^ h * realRank R.entry) (i : ℕ) :
    let d₀ := Nat.log 2 (pow2 (64 * (L + 1))) + 1
    let Ri := round^[i] (initialMatrix L)
    (yes → Dcost Ri.entry ≤ d₀ + i * h) ∧
      (no → Dcost Ri.entry = d₀ + i * h + i ∧
        DeletionBounds Ri.entry Ri.μX Ri.μY (1 / 2 ^ L) ((d₀ + i * h + i : ℕ) : ℤ)) ∧
      realRank Ri.entry ≤ 2 ^ (d₀ + i * h - 1) ∧ Dcost Ri.entry ≤ d₀ + i * h + i := by sorry

end DetCCHard
