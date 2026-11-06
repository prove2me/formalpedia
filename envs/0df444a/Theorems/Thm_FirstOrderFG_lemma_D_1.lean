-- Prove2me | Theorems.Thm_FirstOrderFG_lemma_D_1
-- name    : FirstOrderFG.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:29.380798+00:00
-- url     : https://prove2.me/theorems/d95bbcb1-25fc-4d23-b6da-3a5f9c38ae6d
-- title:
--   Lemma D.1 (Lemma 1 of [KNVM14]) — $\sum_i p_i/(c+\sum_{j\to i}p_j)\le2\alpha'\ln(1+(\lceil d^2/c\rceil+d)/\alpha')+2$
-- statement:
--   Let $G'=(V',E')$ be a self-aware directed graph (every vertex has a self-loop) on $d=|V'|\ge1$ vertices, with independence number $\alpha'$. For every $c>0$ and nonnegative numbers $(p_i)_{i\in V'}$ with $\sum_{i\in V'}p_i\le1$,
--   $$
--   \sum_{i\in V'}\frac{p_i}{c+\sum_{j\in V':\,j\to i}p_j}\ \le\ 2\alpha'\ln\Big(1+\frac{\lceil d^2/c\rceil+d}{\alpha'}\Big)+2 .
--   $$
--
--   This graph-theoretic bound, due to Kocák, Neu, Valko and Munos, controls the cost of importance-weighted loss estimation by the independence number; the paper derives Lemma 2.1 from it.
--
--   Differences from the source:
--   - encoding: $|V'|=d$ → $V'$ nonempty ($d\ge1$); reason: for $d=0$ the right-hand side divides by $\alpha'=0$ and is undefined; this excludes only that case
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma D.1, p.37 (Lemma 1 of [KNVM14], case m = 1)

import Mathlib
import Definitions.Def_FirstOrderFG_indepNumber

namespace FirstOrderFG

/-- **Lemma D.1 (Lemma 1 of [KNVM14]).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma D.1, p.37:
"Let `G′ = (V′, E′)` be a self-aware directed graph with `|V′| = d`, and denote by `α′` its
independence number. For every `c > 0` and nonnegative numbers `(p_i)_{i ∈ V′}` with
`∑_{i ∈ V′} p_i ≤ 1`, we have
`∑_{i ∈ V′} p_i / (c + ∑_{j ∈ V′ : j → i} p_j) ≤ 2α′ ln(1 + (⌈d²/c⌉ + d)/α′) + 2`."

**Formalization Note.** The graph is a relation `E'` on a finite type `V` with a self-loop at every
vertex (self-aware); `E' j i` is `j → i`. `V` is nonempty (`d ≥ 1`), so `α′ ≥ 1`. `⌈·⌉` is
`Nat.ceil`; `ln` is `Real.log`. -/
theorem lemma_D_1 {V : Type} [Fintype V] [Nonempty V] (E' : V → V → Prop) [DecidableRel E']
    (hself : ∀ i, E' i i) (c : ℝ) (hc : 0 < c) (p : V → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i ≤ 1) :
    ∑ i, p i / (c + ∑ j ∈ Finset.univ.filter (fun j => E' j i), p j)
      ≤ 2 * (indepNumber E' : ℝ) * Real.log (1 + (((⌈(Fintype.card V : ℝ) ^ 2 / c⌉₊ : ℕ) : ℝ)
          + Fintype.card V) / indepNumber E') + 2 := by sorry

end FirstOrderFG
