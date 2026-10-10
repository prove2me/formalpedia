-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_momentSum_eq_sum_pathPhi
-- name    : ArtinPrimitiveRoots.momentSum_eq_sum_pathPhi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:24:03.164326+00:00
-- url     : https://prove2.me/theorems/5d8387cc-e16c-4aaf-9236-b5b6f0decd33
-- title:
--   [21] (3.30)–(3.32) — the moment Σ_P⟨u_P, (AA*)^R u_P⟩ is the sum over primitive roots P₀ of the path functional in root coordinates
-- statement:
--   Assume the prime groups are pairwise disjoint, $R \ge 1$ and $U, V \ge 1$. Then `momentSum x a A₀ Y J R d₀ U V` equals the sum over the primitive positions $P_0 = (u, v)$ of the box `posBox U V` of `pathPhi`. Here `pathPhi` is evaluated for the parameters with path length $N = 2R$ (the memory bound $B$ is arbitrary), at the root $(u, v, r_{P_0})$, with the divisibility oracle $p \mid uz_1 + cz_2$, where $c \equiv -v^{-1} \pmod u$. This is an exact identity.
--
--   The objects are in the bundles `Def_ArtinMinorOperator` and `Def_ArtinMemoryModel`.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), pp. 17–18, (3.30)–(3.32).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 17–18, (3.30)–(3.32)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel

namespace ArtinPrimitiveRoots

open Finset

theorem momentSum_eq_sum_pathPhi (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (A₀ Y : ℝ) (J R d₀ : ℕ)
    (U V : ℝ) (B : ℕ)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (primeGroup x (a i)) (primeGroup x (a i')))
    (hR : 1 ≤ R) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    momentSum x a A₀ Y J R d₀ U V =
      ∑ P₀ ∈ posBox U V,
        (⟨x, K, a, A₀, Y, J, 2 * R, d₀, U, V, B⟩ : MemParams).pathPhi (rootOf P₀) (physDelta P₀) := by
  sorry

end ArtinPrimitiveRoots
