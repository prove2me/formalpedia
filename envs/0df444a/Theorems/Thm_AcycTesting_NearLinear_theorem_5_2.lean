-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_theorem_5_2
-- name    : AcycTesting.NearLinear.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:45.133206+00:00
-- url     : https://prove2.me/theorems/5c08ce4d-ea1e-4e35-8b9a-799ea5c19396
-- title:
--   Theorem 5.2 — forest comparison: |log Emb_G(F) − log Emb_G′(F)| ≤ 8e c(2eκ)^K, with equality of counts if c ≤ K
-- statement:
--   Let $K,\Lambda\ge1$ be integers, and let $G,G'$ be permutation cores on $N$ vertices with weak girth greater than $2K\Lambda+1$. Let $F$ be a proper coloured forest with $c$ components, each with at most $S$ vertices and weak diameter at most $\Lambda$. If $\kappa=cS^2/N\le1/(16e^2)$, then both embedding counts are positive and
--   $$\big|\log\mathrm{Emb}_G(F)-\log\mathrm{Emb}_{G'}(F)\big|\ \le\ 8e\,c\,(2e\kappa)^K,\tag{5.1}$$
--   and $\mathrm{Emb}_G(F)=\mathrm{Emb}_{G'}(F)$ if $c\le K$. Here $\mathrm{Emb}_G(F)$ is the number of injective maps $V(F)\to V(G)$ preserving the direction and colour of every edge. This is the counting estimate that makes the random NO core and the periodic YES core indistinguishable on forest-shaped observations.
--
--   Differences from the source:
--   - encoding: G, G′ permutation cores on N vertices → P : CoreMaps V, P′ : CoreMaps V′ on Fintypes with card N (possibly different types), each map bijective; reason: an N-vertex core on any N-set; the statement is invariant under relabelling
--   - encoding: κ = cS²/N, N vertices → 0 < N assumed; reason: κ is undefined at N = 0; this excludes only the undefined case
--   - encoding: F with c components, each with at most S vertices and weak diameter at most Λ → numComponents F = c (weak components of the underlying graph), ComponentsBounded F S Λ with S real; reason: the source's S need not be an integer (S = N^z in Theorem 5.1)
--   - generalization: (5.1) and the equality clause → additionally 0 < Emb_G(F) and 0 < Emb_G′(F); reason: Real.log is total and the log inequality alone does not assert positive counts; positivity holds under the hypotheses (Emb = N^c Φ_G(F) by (6.1) and Φ_G(F) = Φ_[c](a(G)) > 0 by (6.3), Lemmas 6.1 and 6.3), so the statement specializes to the source's
--   - encoding: log → Real.log (natural logarithm) of the counts cast to ℝ; reason: §3.1: logarithms are natural
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 18 (PDF 21), Theorem 5.2

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_PermCores
import Definitions.Def_AcycTesting_NearLinear_Forests

namespace AcycTesting.NearLinear

/-- Theorem 5.2 (forest comparison), with the positivity of both embedding counts. -/
theorem theorem_5_2 {U V V' : Type*} [Fintype U] [Fintype V] [Fintype V'] (K Λ : ℕ)
    (hK : 1 ≤ K) (hΛ : 1 ≤ Λ) (N : ℕ) (hN : 0 < N)
    (hV : Fintype.card V = N) (hV' : Fintype.card V' = N)
    (P : CoreMaps V) (P' : CoreMaps V') (hP : IsPermCore P) (hP' : IsPermCore P')
    (hgirth : CoreGirthGT P (2 * K * Λ + 1)) (hgirth' : CoreGirthGT P' (2 * K * Λ + 1))
    (F : ColGraph U) (hprop : IsProperCol F) (hfor : IsColForest F) (c : ℕ) (S : ℝ)
    (hc : numComponents F = c) (hS : ComponentsBounded F S Λ)
    (hκ : (c : ℝ) * S ^ 2 / N ≤ 1 / (16 * Real.exp 1 ^ 2)) :
    0 < Emb P F ∧ 0 < Emb P' F ∧
      |Real.log (Emb P F) - Real.log (Emb P' F)| ≤
        8 * Real.exp 1 * c * (2 * Real.exp 1 * ((c : ℝ) * S ^ 2 / N)) ^ K ∧
      (c ≤ K → Emb P F = Emb P' F) := by sorry

end AcycTesting.NearLinear
