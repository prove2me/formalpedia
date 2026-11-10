-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_A_1
-- name    : AcycTesting.NearLinear.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:35:51.403515+00:00
-- url     : https://prove2.me/theorems/07e14c3a-aea6-4d9c-b218-7790b7c75925
-- title:
--   Lemma A.1 — the expected number of weak cycles of length at most γ in Γ(Π) is at most 4·64^γ
-- statement:
--   Let $\gamma=\gamma(N)$ satisfy (3.1): $\gamma(N)\ge2$ and $64^{\gamma}\log N=o(N)$. For $\Pi=(\pi_1,\dots,\pi_{32})$ independent uniform permutations of $[N]$, let $\mathrm{cyc}_{\le\gamma}(\Pi)$ be the number of weak cycles of length at most $\gamma$ in the occurrence graph $\Gamma(\Pi)$ (one occurrence $v\to\pi_a(v)$ per vertex and colour; loops count as weak cycles of length one, two occurrences on one pair as weak cycles of length two). Then for all sufficiently large even $N$,
--   $$\mathbb E\,\mathrm{cyc}_{\le\gamma}(\Pi)\le 4\cdot 64^{\gamma}.$$
--   This bounds the number of short cycles a switching argument has to remove (Proposition 3.1).
--
--   Differences from the source:
--   - encoding: (3.1): an integer γ = γ(N) ≥ 2 with 64^γ log N = o(N) → GirthScale γ: γ : ℕ → ℕ, γ N ≥ 2 for all N, and 64^(γ N) · log N / N → 0; reason: the meaning of o(N) along N → ∞, natural log (§3.1)
--   - encoding: N even (standing assumption of §3.2), [N], colours [32] → Even N, Fin N, Fin 32 (0-based colours); reason: Lean convention; the same tuples
--   - encoding: Pr / E over independent uniform permutations π1, …, π32 → probU / expU: uniform on PermTuple N = Fin 32 → Equiv.Perm (Fin N); reason: the product of independent uniform laws is uniform on tuples
--   - encoding: weak cycles of the underlying undirected multigraph of Γ(Π) → IsWeakCycle (coreEnds (occMaps Π)) S: a set S of j ≥ 1 distinct occurrences on j distinct vertices, cyclically joined in either direction; reason: loops are length 1 and two occurrences on one pair length 2, as in §3.1; cycles counted as occurrence sets
--   - encoding: for all large N → ∃ N₀, ∀ N ≥ N₀ (N even); reason: meaning of "all large N"
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 38 (PDF 41), Lemma A.1

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_Digraphs
import Definitions.Def_AcycTesting_NearLinear_PermCores

namespace AcycTesting.NearLinear

/-- Lemma A.1 (cycle count): under (3.1), for all large even `N`, the expected number of weak
cycles of length at most `γ(N)` in `Γ(Π)` is at most `4 · 64^{γ(N)}`. -/
theorem lemma_A_1 (γ : ℕ → ℕ) (hγ : GirthScale γ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      expU (fun πs : PermTuple N => (cycLe πs (γ N) : ℝ)) ≤ 4 * (64 : ℝ) ^ (γ N) := by sorry

end AcycTesting.NearLinear
