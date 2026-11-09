-- Prove2me | Theorems.Thm_DerandLDT_lemma_3_18
-- name    : DerandLDT.lemma_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:04:41.28652+00:00
-- url     : https://prove2.me/theorems/8ab3f7a2-a989-4164-b92d-1b04be1de9dc
-- title:
--   Lemma 3.18 — pruning a bipartite graph to minimum degrees $\varepsilon\ell/10$ and $\delta r/10$
-- statement:
--   Let $G = (U, V, E)$ be a finite bipartite graph in which every vertex of $U$ has degree at most $\ell$ and every vertex of $V$ has degree at most $r$, where $\ell, r > 0$. Suppose the average degree of a vertex of $U$ is $\varepsilon\ell$ and the average degree of a vertex of $V$ is $\delta r$, that is, $|E| = \varepsilon\ell|U| = \delta r|V|$. Then there are $U' \subseteq U$ and $V' \subseteq V$ such that
--
--   1. $|U'| \ge \frac{4\varepsilon}{5}|U|$ and $|V'| \ge \frac{4\delta}{5}|V|$;
--   2. in the subgraph $G'$ induced on $U' \cup V'$, every vertex of $U'$ has degree at least $\varepsilon\ell/10$ and every vertex of $V'$ has degree at least $\delta r/10$.
--
--   In the analysis of the derandomized test this is applied to the points-vs-lines graph of accepted incidences to obtain the good points and good lines (Corollary 6.1).
--
--   **Formalization Note** The graph is an edge set $E \subseteq U \times V$ of finite sets; degrees in $G'$ count the $E$-neighbours inside $V'$ (resp. $U'$).
--
--   Differences from the source:
--   - reading: "the degree of every vertex in R′" → every vertex of V′; reason: R′ is a typo; the graph has parts U′ and V′
--   - reading: a subgraph G′ = (U′, V′, E′) of G → the subgraph induced on U′ ∪ V′ (E′ = E ∩ U′ × V′); reason: the strongest reading of subgraph; any subgraph's degrees are at most the induced ones
--   - encoding: the average degree of a vertex in U is εℓ, in V is δr → |E| = εℓ|U| and |E| = δr|V|; reason: cross-multiplied form of the averages
--   - encoding: parameters ℓ, r → real ℓ, r with 0 < ℓ and 0 < r; reason: for ℓ = 0 (or r = 0) the parameter ε (or δ) is not determined by the graph and the averages say nothing
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 3.18, p.15

import Mathlib

set_option autoImplicit false

universe u

namespace DerandLDT

/-- **Lemma 3.18** (pruning to a subgraph of high minimum degree). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point low-degree test*,
STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Lemma 3.18, p.15:
*Let `G = (U, V, E)` be a bipartite graph in which every vertex of `U` has degree at most `ℓ` and
every vertex of `V` degree at most `r`, and in which the average degree of a vertex of `U` is
`εℓ` and of a vertex of `V` is `δr`. Then there is a subgraph `G′ = (U′, V′, E′)` with
`|U′| ≥ (4ε/5)|U|`, `|V′| ≥ (4δ/5)|V|`, every vertex of `U′` of degree at least `εℓ/10` in
`G′` and every vertex of `V′` of degree at least `δr/10` in `G′`.*

**Formalization Note.** The graph is a finite edge set `E ⊆ U ×ˢ V`; the average degrees are
stated as `|E| = εℓ|U|` and `|E| = δr|V|`. `G′` is the subgraph induced on `U′ ∪ V′` (the
strongest reading of "subgraph"), so degrees in `G′` count `E`-neighbours inside `V′`
(resp. `U′`). The printed "every vertex in `R′`" is read as `V′`. The bounds `ℓ, r` are real
numbers with `0 < ℓ`, `0 < r`: for `ℓ = 0` the parameter `ε` is not determined by the graph. -/
theorem lemma_3_18 {α β : Type u} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (E : Finset (α × β)) (hE : E ⊆ U ×ˢ V)
    (ℓ r : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r)
    (hdegU : ∀ u ∈ U, ((E.filter fun e => e.1 = u).card : ℝ) ≤ ℓ)
    (hdegV : ∀ v ∈ V, ((E.filter fun e => e.2 = v).card : ℝ) ≤ r)
    (ε δ : ℝ) (hε : (E.card : ℝ) = ε * ℓ * U.card) (hδ : (E.card : ℝ) = δ * r * V.card) :
    ∃ U' ⊆ U, ∃ V' ⊆ V,
      4 * ε / 5 * (U.card : ℝ) ≤ U'.card ∧ 4 * δ / 5 * (V.card : ℝ) ≤ V'.card ∧
      (∀ u ∈ U', ε * ℓ / 10 ≤ ((V'.filter fun v => (u, v) ∈ E).card : ℝ)) ∧
      (∀ v ∈ V', δ * r / 10 ≤ ((U'.filter fun u => (u, v) ∈ E).card : ℝ)) := by sorry

end DerandLDT
