-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_corollary_1
-- name    : CapacitatedKMedianFPT.Main.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:05.719023+00:00
-- url     : https://prove2.me/theorems/df95d931-cbb5-4cc9-81bb-19f69c272885
-- title:
--   Corollary 1 — v(Fix(L)) ≥ E[v(R_L)]
-- statement:
--   Let $F=F_1\cup\dots\cup F_k$ with disjoint parts and $v$ monotone submodular. For any tuple $L=(L_1,\dots,L_k)$ of lists with $|L_i|=N$ for all $i$ and entries of $L_i$ in $F_i$,
--   $$v(\mathrm{Fix}(L))\ge\mathbb E[v(R_L)],$$
--   where $R_L$ includes every occurrence of every list independently with probability $\eta=1/N$ (duplicates removed), and $\mathrm{Fix}(L)$ is any choice of one entry per list maximizing $v$.
--
--   This shows that the final enumeration of Algorithm 2 loses nothing against the fractional solution.
--
--   Differences from the source:
--
--   - generalization: v the normalized monotone submodular v : 2^F → ℚ≥0 of Theorem 4, N = ⌈2k/ε⌉ → any monotone submodular v : 2^F → ℝ and any N ≥ 1; reason: the source's v and N are special cases; the proof uses only Lemma 7's hypotheses
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 18, Corollary 1 and proof; p. 16, R_i, R_L; p. 17, Algorithm 4 (Fix)

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_RandomSets
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Corollary 1** (p. 18). For lists `L_1, …, L_k` of length `N ≥ 1` with entries of `L_i` in
`F_i`, every output of `Fix(L)` has value at least `E[v(R_L)]`, where `R_L` includes every occurrence
independently with probability `η = 1/N`. -/
theorem corollary_1 {α : Type} [Fintype α] [DecidableEq α] (k N : ℕ) (hN : 1 ≤ N)
    (F : Fin k → Finset α)
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j))) (hcover : ∀ x, ∃ i, x ∈ F i)
    (v : Finset α → ℝ) (hmono : SubsamplingSM.Offline.IsMonotoneSetFn v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (L : Fin k → List α) (hlen : ∀ i, (L i).length = N) (hmem : ∀ i, ∀ x ∈ L i, x ∈ F i)
    (x : Fin k → α) (hx : IsFixOutput v L x) :
    expectedRandomValue v (1 / (N : ℝ)) L ≤ v (Finset.univ.image x) := by sorry

end CapacitatedKMedianFPT.Main
