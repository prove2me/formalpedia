-- Prove2me | Theorems.Thm_CompPermOracle_Supplement_theorem_5_3
-- name    : CompPermOracle.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:49:05.755093+00:00
-- url     : https://prove2.me/theorems/5b865172-79fe-4f80-bb9c-354db8dc5df9
-- title:
--   Theorem 5.3 — explicit search bound $p\le\min\{1,(2\sqrt2\sum_t\sqrt{s_t/(N-t)}+\ell\sqrt{2/(N-q)}+\delta_N(q+\ell))^2\}$
-- statement:
--   Suppose a quantum algorithm makes $q$ forward and/or inverse swap queries to a uniformly random permutation $\varphi$ of $[N]$ and outputs a list of at most $\ell$ input-output pairs. Let $\mathcal B$ be an increasing database property with $\emptyset\notin\mathcal B$, let $s_t$ be its two-sided sparsity, and let $p$ be the probability that the output list witnesses $\mathcal B$ and every listed pair agrees with $\varphi$. If $3(q+\ell)-1\le N$, then
--   $$
--   p\le\min\Big\{1,\Big(2\sqrt2\sum_{t=0}^{q-1}\sqrt{\frac{s_t}{N-t}}+\ell\sqrt{\frac{2}{N-q}}+\delta_N(q+\ell)\Big)^2\Big\}.
--   $$
--   The same bound holds in the ideal cipher model with any finite key space $\mathcal K$: the algorithm may query $\varphi_k$ and $\varphi_k^{-1}$ under keys of its choice, in superposition; it outputs a list of at most $\ell$ triples $(k,x,y)$; $\mathcal B$ is an increasing property of keyed databases not containing the empty keyed database; $p$ is the probability that the list witnesses $\mathcal B$ and $\varphi_k(x)=y$ for every listed triple; and $s_t$ is the keyed sparsity.
--
--   This is an explicit-constant form of the general compressed-oracle search bound: it combines the fundamental lemma (Lemma 5.1) with the bound on creating a satisfying database (Lemma 5.2), and it is the tool behind the sponge and Davies–Meyer bounds (Theorems 5.5 and 5.6).
--
--   **Formalization Note** Algorithms are the published `Alg` (forward and inverse swap queries coherently controlled on a direction bit); keyed algorithms carry the key register in the workspace. The two settings are the two clauses of one conjunction.
--
--   Differences from the source:
--   - reading: a list witnesses 𝓑 if it is consistent with a partial permutation belonging to 𝓑 → the set of pairs (triples) of the list is exactly the graph of some member of 𝓑; reason: the proof of Lemma 5.1 (p.28) uses that a database containing a witnessing list belongs to 𝓑, i.e. this reading plus monotonicity; the containment reading makes the theorem false (N = 10^6, q = ℓ = 1, 𝓑 = {f : |f| ≥ N − 1}, output (0, φ(0)): p = 1 against a bound ≈ 0.015)
--   - encoding: p is measured on the purification → p is the classically sampled real experiment, (N!)^{-1} Σ_φ (resp. (N!)^{-|𝒦|} Σ_Φ) over the measured accessible outcomes; reason: equal by Remark 3.3 (published CompPermOracle.remark_3_3); keyed analogue keywise
--   - encoding: an algorithm making at most q queries and outputting a list → a published Alg run for exactly q queries, with an output map out from the measured accessible basis state to a list of length ≤ ℓ for every outcome; reason: an algorithm with fewer queries is a q-query algorithm that ignores the extra answers; a measured output is a function of the computational-basis outcome of a large enough workspace
--   - encoding: ideal cipher algorithm with key register → Alg N (K × W) with the accessible key register first in the workspace; each query applies Õ_{φ_k} / Õ_{φ_k^{-1}} controlled on (direction, key); reason: the key is chosen by the adversary and queried in superposition, and the oracle is inaccessible, as in §3.2
--   - encoding: 3(q + ℓ) − 1 ≤ N; N − t, N − q real → 3 * (q + ℓ) ≤ N + 1 in ℕ; every difference cast to ℝ; maxima in s_t over empty sets are 0; reason: same instances; no truncated subtraction
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Theorem 5.3, eq. (86), p.29 (hypotheses: Lemma 5.1, p.27; s_t: eq. (84), pp.28–29)

import Mathlib
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_Alg
import Definitions.Def_CompPermOracle_Supplement_deltaN
import Definitions.Def_CompPermOracle_Supplement_sparsity
import Definitions.Def_CompPermOracle_Supplement_keyedState

namespace CompPermOracle.Supplement

open CompPermOracle

/-- **Theorem 5.3 (Explicit search bound)** (Carolan, Majenz, Compressed Permutation Oracles
Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Theorem 5.3, eq. (86), p.29).
Under the hypotheses of Lemma 5.1 (p.27; printed "Theorem 5.1"), with `∅ ∉ 𝓑`,
`p ≤ min{1, (2√2 ∑_{t=0}^{q−1} √(s_t/(N − t)) + ℓ√(2/(N − q)) + δ_N(q + ℓ))²}`.

Clause (a) is the random permutation model; clause (b) is the ideal cipher model, which Lemma 5.1's
last sentence brings under "the hypotheses of Theorem 5.1": lists of triples `(k, x, y)`, keyed
increasing properties and the keyed sparsity.

**Formalization Note.** A `q`-query algorithm is the published `Alg` run for `q` queries (forward
and inverse swap queries, coherently controlled on a direction bit), with an output map `out` from
the measured accessible basis state to a list of at most `ℓ` pairs; a keyed algorithm is an
`Alg N (K × W)` whose workspace starts with the key register. `p` is the probability, over a uniform
`φ` (resp. a uniform `Φ`), that the list witnesses `𝓑` and every pair (triple) agrees with the
oracle. The hypothesis `3(q + ℓ) − 1 ≤ N` is written `3(q + ℓ) ≤ N + 1` in `ℕ`; every `N − t` is
real. `∅` is `⊥`. -/
theorem theorem_5_3 :
    (∀ {N : ℕ} {W : Type} [Fintype W] [DecidableEq W] (A : Alg N W) (q ℓ : ℕ)
        (out : Acc N W → List (Fin N × Fin N)), (∀ c, (out c).length ≤ ℓ) →
        ∀ B : Set (PartialPerm N), Increasing B → (⊥ : PartialPerm N) ∉ B →
        3 * (q + ℓ) ≤ N + 1 →
        realSuccess A q out (fun l φ => Witnesses B l ∧ Agrees φ l) ≤
          min 1 ((2 * Real.sqrt 2 *
              ∑ t ∈ Finset.range q, Real.sqrt ((sparsity B t : ℝ) / ((N : ℝ) - t)) +
            (ℓ : ℝ) * Real.sqrt (2 / ((N : ℝ) - q)) + deltaN N (q + ℓ)) ^ 2)) ∧
    (∀ {N : ℕ} {K W : Type} [Fintype K] [DecidableEq K] [Fintype W] [DecidableEq W]
        (A : Alg N (K × W)) (q ℓ : ℕ) (out : Acc N (K × W) → List (K × Fin N × Fin N)),
        (∀ c, (out c).length ≤ ℓ) →
        ∀ B : Set (K → PartialPerm N), KIncreasing B → (fun _ => (⊥ : PartialPerm N)) ∉ B →
        3 * (q + ℓ) ≤ N + 1 →
        keyedSuccess A q out (fun l Φ => KWitnesses B l ∧ KAgrees Φ l) ≤
          min 1 ((2 * Real.sqrt 2 *
              ∑ t ∈ Finset.range q, Real.sqrt ((keyedSparsity B t : ℝ) / ((N : ℝ) - t)) +
            (ℓ : ℝ) * Real.sqrt (2 / ((N : ℝ) - q)) + deltaN N (q + ℓ)) ^ 2)) := by sorry

end CompPermOracle.Supplement
