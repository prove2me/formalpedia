-- Prove2me | Theorems.Thm_DraftPoA_headline
-- name    : DraftPoA.headline
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:32.072007+00:00
-- url     : https://prove2.me/theorems/3a229f14-9f20-445e-9443-6db54262fcfa
-- title:
--   The price of anarchy of the draft auction is $(1\pm o(1))\ln m/\ln\ln m$
-- statement:
--   The paper's headline, as the conjunction of Corollary 3.4, Theorem 4.1 and Remark B.7 (i). Write $B(m)=\bigl(1+\frac{13\ln\ln\ln m}{\ln\ln m}\bigr)\frac{\ln m}{\ln\ln m}+3$ and $H_N$ for the $N$-th harmonic number.
--
--   1. **(A) Headline.** With continuous bids ($\delta=0$), for pure Nash, mixed Nash, correlated and Bayes–Nash equilibria, and for additive as well as monotone subadditive bidders,
--   $$\frac{\mathrm{PoA}(m)}{\ln m/\ln\ln m}\ \longrightarrow\ 1\qquad(m\to\infty).$$
--   2. **(B) Corollary 3.4.** For $m\ge10^{2407}$, those four concepts and subadditive bidders: $\mathrm{PoA}\le B(m)$ at $\delta=0$; and for every $\delta>0$ every equilibrium has $\mathbb E[\mathrm{OPT}]-4m\delta\le B(m)\,\mathbb E[\mathrm{SW}]$.
--   3. **(C) Theorem 4.1, first statement.** There is a constant $C$ such that for every $N\ge4$ the instance with $m(N)=N+r\le C\,N\ln N\ln\ln N$ items has additive bidders, one of whom values nothing, a priority order, bid increment $\delta_N=1/(4N^2\lceil H_N\rceil^2)$ and cap $\bar M=1$, and a pure subgame-perfect equilibrium $b$ with
--   $$\frac{\mathrm{OPT}}{\mathrm{SW}(b)}\ \ge\ \frac{H_N}{\ln(H_N+1)+6}.$$
--   4. **(D) Theorem 4.1, "Consequently".** There are $C$ and $m_0$ such that for every $m\ge m_0$, with $N$ the largest integer with $m(N)\le m$, every integer $k\ge1$ and every equilibrium concept (pure Nash, mixed Nash, correlated, Bayes–Nash, pure SPE), the price of anarchy with $m$ items and additive bidders on the grid $\delta_N/k$ is at least $\bigl(1-\frac{C}{\ln\ln m}\bigr)\frac{\ln m}{\ln\ln m}$.
--   5. **(E) Remark B.7 (i).** There are $C$ and $m_0$ such that the same lower bound holds with continuous bids for pure Nash, mixed Nash, correlated and Bayes–Nash equilibria.
--
--   This settles the question of Devanur, Morgenstern and Syrgkanis: the price of anarchy of the draft auction for subadditive bidders is not a constant, and its order is $\ln m/\ln\ln m$ already for additive bidders.
--
--   **Formalization Note** PoA is the supremum over all numbers of bidders, priority orders, caps, instances of the class and equilibria, computed in $[0,\infty]$; (A) takes its real value. The ratio of (C) is written multiplied out with $\mathrm{SW}(b)>0$.
--
--   Differences from the source:
--   - reading: the headline "the price of anarchy is (1 ± o(1)) ln m/ln ln m" (no single numbered statement) → the conjunction of Corollary 3.4, Theorem 4.1 and Remark B.7 (i), with the limit (A) at δ = 0; reason: Corollary 3.4 is the upper half, Theorem 4.1 the lower half; δ = 0 is the only grid on which both bounds are ratios (Remark B.7 (i))
--   - reading: expectations under mixed, correlated and Bayes–Nash equilibria (with δ = 0 the strategy space carries no usable σ-algebra) → probability spaces mapping to pure profiles with a measurable outcome map; deviations unrestricted; the inequality in lower-integral form; reason: agrees with the printed inequality whenever the deviation's expectation is defined; the paper asks for measurable strategies so that expectations are defined (p.18)
--   - generalization: in the Bayesian setting the type is the valuation v_i itself, drawn from F_i, and b_i maps types to (pure or mixed) strategies → an arbitrary measurable type space T_i with prior F_i, valuations V_i t measurable in t, and a mixing device (Ω_i, μ_i) with b_i : T_i → Ω_i → Strategy; reason: T_i = the valuations with V_i = id (a one-point device for pure strategies) is the source's setting, so the upper bound specializes to it; the lower bounds are attained at one-point type spaces, where the two coincide
--   - encoding: PoA = sup E[OPT]/E[SW] → a supremum in [0, ∞] with a/0 = ∞ for a > 0 and 0/0 = 0; reason: the paper does not discuss 0/0; all its bounds are at least 1
--   - reading: an instance with N sink items and m = O(N ln N ln ln N) items in all, bids at most M̄ → an instance on exactly m(N) = N + r items, with M̄ = 1, and a constant C with m(N) ≤ C N ln N ln ln N; reason: §4.1 fixes m = N + r and M̄ = 1; (D) refers to "the largest instance above", which needs m(N)
--   - reading: every equilibrium concept of Section 2 (SPE in behavior strategies) → pure Nash, mixed Nash, correlated, Bayes–Nash and pure SPE; reason: the equilibrium is a pure SPE, and a pure SPE is an SPE in behavior strategies, so the bound for pure SPE gives the one for SPE
--   - reading: Remark B.7 (i): the lower bound for Nash equilibria with continuous bids → (E) for pure Nash, mixed Nash, correlated and Bayes–Nash; reason: §2, p.5: a pure Nash equilibrium is a mixed Nash, correlated and Bayes–Nash equilibrium; (A) needs all four
--   - encoding: o(1), O(1/ln ln m) → Tendsto along m → ∞; constants C and m₀ quantified before m; reason: the meaning of the asymptotic notation
--   - encoding: OPT/SW(b) ≥ X → X · SW(b) ≤ OPT with SW(b) > 0; reason: equivalent; avoids real division
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), abstract, p.1 (PDF 1); Corollary 3.4 and Theorem 4.1, p.9 (PDF 10); Remark B.7 (i), p.23 (PDF 24)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria
import Definitions.Def_DraftPoA_BadInstance

open Filter Topology

namespace DraftPoA

/-- The headline of the abstract (PDF p.1: "the price of anarchy is (1 ± o(1)) ln m/ln ln m"),
as the conjunction of Corollary 3.4 (p.9, PDF 10), Theorem 4.1 (p.9, PDF 10) and Remark B.7 (i)
(p.23, PDF 24) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

* (A) With continuous bids (`δ = 0`), for pure Nash, mixed Nash, correlated and Bayes–Nash
  equilibria and for additive as well as monotone subadditive bidders,
  `PoA / (ln m/ln ln m) → 1` as `m → ∞`.
* (B) Corollary 3.4: for `m ≥ 10^2407` and those four concepts, with subadditive bidders,
  `PoA ≤ (1 + 13 ln ln ln m/ln ln m) ln m/ln ln m + 3` at `δ = 0`; for `δ > 0` the same bound holds
  with `E[OPT] − 4mδ` in place of `E[OPT]`.
* (C) Theorem 4.1, first statement: for every `N ≥ 4` the instance with `m(N) = N + r` items
  (`m(N) = O(N ln N ln ln N)`), additive bidders one of whom values nothing, a priority order, bid
  increment `δ_N = 1/(4N²⌈H_N⌉²)` and cap `M̄ = 1` has a pure SPE `b` with
  `OPT/SW(b) ≥ H_N/(ln(H_N + 1) + 6)`.
* (D) Theorem 4.1, "Consequently": for every equilibrium concept, the PoA with `m` items and
  additive bidders is at least `(1 − O(1/ln ln m)) ln m/ln ln m` for the bid increment `δ_N` of the
  largest instance with at most `m` items and for every `δ_N/k`, `k ≥ 1` an integer.
* (E) Remark B.7 (i): the same lower bound with continuous bids, for the Nash-type concepts.

**Formalization Note.** PoA is `poa` (a supremum in `ℝ≥0∞` over all numbers of bidders, priority
orders, caps, instances of the class and equilibria). `o(1)` is a limit along `m → ∞`; `O(·)` is a
constant `C` (with a threshold `m₀`) quantified before `m`. The ratio of (C) is multiplied out with
`SW(b) > 0`. "Every equilibrium concept of Section 2" is read with pure SPE in place of SPE in
behavior strategies: a pure SPE is one, so the bound for pure SPE implies the one for SPE. -/
theorem headline :
    (∀ c : Concept, c ≠ Concept.pureSPE → ∀ cls : ValClass,
      Tendsto (fun m : ℕ => (poa c cls m 0).toReal / (Real.log m / Real.log (Real.log m)))
        atTop (𝓝 1)) ∧
    (∀ m : ℕ, 10 ^ 2407 ≤ m → ∀ c : Concept, c ≠ Concept.pureSPE →
      poa c ValClass.subadditive m 0 ≤ ENNReal.ofReal
        ((1 + 13 * Real.log (Real.log (Real.log m)) / Real.log (Real.log m)) *
          (Real.log m / Real.log (Real.log m)) + 3) ∧
      ∀ δ : ℝ, 0 < δ → ∀ x ∈ outcomes c ValClass.subadditive m δ,
        x.1 - 4 * (m : ℝ) * δ ≤
          ((1 + 13 * Real.log (Real.log (Real.log m)) / Real.log (Real.log m)) *
            (Real.log m / Real.log (Real.log m)) + 3) * x.2) ∧
    (∃ C : ℝ, ∀ N : ℕ, 4 ≤ N →
      (mOf N : ℝ) ≤ C * N * Real.log N * Real.log (Real.log N) ∧
      ∃ (n : ℕ) (_ : NeZero n) (prio : Equiv.Perm (Fin n))
        (v : Fin n → Finset (Fin (mOf N)) → ℝ) (b : Fin n → Strategy n (mOf N) (deltaOf N) 1),
        (∀ i, IsAdditive (v i)) ∧ (∃ i, ∀ S, v i S = 0) ∧ IsCapped v 1 ∧
        IsPureSPE prio v b ∧ 0 < SW prio v b ∧
        (harmonic N : ℝ) / (Real.log ((harmonic N : ℝ) + 1) + 6) * SW prio v b ≤ OPT v) ∧
    (∃ (C : ℝ) (m₀ : ℕ), ∀ m : ℕ, m₀ ≤ m → ∀ N : ℕ,
      IsGreatest {N : ℕ | 4 ≤ N ∧ mOf N ≤ m} N → ∀ k : ℕ, 1 ≤ k → ∀ c : Concept,
        ENNReal.ofReal ((1 - C / Real.log (Real.log m)) * (Real.log m / Real.log (Real.log m))) ≤
          poa c ValClass.additive m (deltaOf N / k)) ∧
    (∃ (C : ℝ) (m₀ : ℕ), ∀ m : ℕ, m₀ ≤ m → ∀ c : Concept, c ≠ Concept.pureSPE →
      ENNReal.ofReal ((1 - C / Real.log (Real.log m)) * (Real.log m / Real.log (Real.log m))) ≤
        poa c ValClass.additive m 0) := by sorry

end DraftPoA
