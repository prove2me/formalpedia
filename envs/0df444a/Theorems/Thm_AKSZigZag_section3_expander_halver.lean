-- Prove2me | Theorems.Thm_AKSZigZag_section3_expander_halver
-- name    : AKSZigZag.section3_expander_halver
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:32.580097+00:00
-- url     : https://prove2.me/theorems/50b2934d-8dad-41cf-99eb-45fc9b6b52e4
-- title:
--   §3, pp.4–5 — the network of an expander's edges is an $\varepsilon$-halver (corrected: expansion up to $\lceil\varepsilon\cdot\mathrm{side}\rceil$)
-- statement:
--   Let $0<\varepsilon<1$, and let $G$ be a bipartite graph between $A=\{1,\dots,\lfloor m/2\rfloor\}$ and $B=\{\lfloor m/2\rfloor+1,\dots,m\}$ such that
--   1. every $X\subseteq A$ with $|X|\le\lceil\varepsilon|B|\rceil$ has $|\Gamma(X)|\ge\frac{1-\varepsilon}{\varepsilon}|X|$;
--   2. every $Y\subseteq B$ with $|Y|\le\lceil\varepsilon|A|\rceil$ has $|\Gamma(Y)|\ge\frac{1-\varepsilon}{\varepsilon}|Y|$.
--
--   Let $N$ be a comparator network whose switches are exactly the edges of $G$: each edge occurs at least once, in any order, and the smaller element goes to $A$. Then $N$ is an $\varepsilon$-halver.
--
--   With the edges grouped into the one-factors of a bounded-valency graph, this gives an $\varepsilon$-halver of bounded depth.
--
--   Differences from the source:
--   - correction: G an expander with parameters ((1−ε)/ε, ε, c), i.e. expansion for |X| ≤ εn → expansion by (1−ε)/ε for |X| ≤ ⌈ε|B|⌉ (X ⊆ A) and |Y| ≤ ⌈ε|A|⌉ (Y ⊆ B); reason: as printed it is false: m = 30, ε = 0.1, a 9-regular bipartite graph in which b₀, b₁ ∈ B share the neighbourhood {a₀,…,a₈} is a (9, 0.1, 9) expander (only singletons must expand), and on the input a₀..a₈ ← 1..9, b₀, b₁ ← 10, 11, a₉..a₁₄ ← 12..17, other b ← 18..30 no switch fires, so two elements of S = (1,…,15) end in B, more than ε|S| = 1.5; the paper's proof needs a set of size ⌈εk⌉
--   - generalization: the network of the c one-factors of the expander (valency ≤ c) → any network whose switches are exactly the edges, in any order, possibly repeated; no valency bound; reason: the valency bound only controls the depth, which this statement does not claim; the one-factor network is such a network
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §3, pp.4–5 ("we obtain a network of depth c. We claim it is an ε-halver.")

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsExpander
import Definitions.Def_AKSZigZag_IsHalver

namespace AKSZigZag

open AKSSorting.Core

/-- **The expander network is an ε-halver** (AKS, STOC 1983, doi:10.1145/800061.808726, §3,
pp.4–5), *corrected*: "Interpreting the edges of a one-factor as switches (performing
comparisons along the edges and always putting the smaller element to A), we obtain a network of
depth c. We claim it is an ε-halver."

Let `0 < ε < 1` and let `E` be a bipartite graph between `A = (1, …, ⌊m/2⌋)` and
`B = (⌊m/2⌋+1, …, m)` such that every `X ⊆ A` with `|X| ≤ ⌈ε|B|⌉` has `|Γ(X)| ≥ ((1-ε)/ε)|X|`,
and every `Y ⊆ B` with `|Y| ≤ ⌈ε|A|⌉` has `|Γ(Y)| ≥ ((1-ε)/ε)|Y|`. Then any comparator network
whose comparators are exactly the edges of `E` (each edge at least once, in any order, smaller
element to `A`) is an ε-halver.

**Formalization Note.** The paper's hypothesis (an expander with parameters `((1-ε)/ε, ε, c)`,
i.e. expansion for `|X| ≤ εn`) is not enough: with `m = 30`, `ε = 0.1`, a 9-regular graph in
which two vertices of `B` share the neighbourhood `{a₀, …, a₈}` is a `(9, 0.1, 9)` expander, yet
on the input `a₀..a₈ ← 1..9`, `b₀, b₁ ← 10, 11`, `a₉..a₁₄ ← 12..17`, other `b ← 18..30` no
comparator fires and two elements of `S = (1, …, 15)` end in `B`. Expansion up to `⌈ε·side⌉`
is what the paper's proof uses. -/
theorem section3_expander_halver {m : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (E : Finset (Fin (m / 2) × Fin (m - m / 2)))
    (hA : ∀ X : Finset (Fin (m / 2)), X.card ≤ ⌈ε * ((m - m / 2 : ℕ) : ℝ)⌉₊ →
      (1 - ε) / ε * X.card ≤ (nbhd E X).card)
    (hB : ∀ Y : Finset (Fin (m - m / 2)), Y.card ≤ ⌈ε * ((m / 2 : ℕ) : ℝ)⌉₊ →
      (1 - ε) / ε * Y.card ≤ (nbhdInv E Y).card)
    (N : ComparatorNetwork m)
    (hN : ∀ L ∈ N.layers, ∀ p ∈ L, ∃ e ∈ E, p = edgeComp e)
    (hE : ∀ e ∈ E, ∃ L ∈ N.layers, edgeComp e ∈ L) :
    IsHalver ε N := by sorry

end AKSZigZag
