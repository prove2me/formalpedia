-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_6_1
-- name    : AcycTesting.NearLinear.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:52.458785+00:00
-- url     : https://prove2.me/theorems/516e1484-c7d7-46b0-8ce0-eb67af4ef20f
-- title:
--   Lemma 6.1 — tree bound for the activities: |a_I(G)| ≤ m^{m−2}(S²/N)^{m−1}
-- statement:
--   Assume the hypotheses of Theorem 5.2 for one core: integers $K,\Lambda\ge1$; a permutation core $G$ on $N\ge1$ vertices with weak girth greater than $2K\Lambda+1$; a proper coloured forest $F$ with $c$ components, each with at most $S$ vertices and weak diameter at most $\Lambda$; and $\kappa=cS^2/N\le 1/(16e^2)$. Fix a root in every component and let $a_I(G)$ be the activity (6.2). Then for every set $I$ of $m=|I|\ge2$ components,
--   $$|a_I(G)|\ \le\ m^{m-2}\Big(\frac{S^2}{N}\Big)^{m-1}.\tag{6.4}$$
--   Each attached component costs a factor $S^2/N$, which makes overlap patterns of many components rare.
--
--   Differences from the source:
--   - encoding: κ = cS²/N, N vertices → 0 < N assumed; reason: κ is undefined at N = 0; this excludes only the undefined case
--   - encoding: F with c components, each with at most S vertices and weak diameter at most Λ → numComponents F = c (weak components of the underlying graph), ComponentsBounded F S Λ with S real; reason: the source's S need not be an integer (S = N^z in Theorem 5.1)
--   - encoding: components F1, …, Fc indexed by [c], fixed roots r_i → components indexed by Mathlib ConnectedComponent of the underlying graph; an arbitrary root function r with r C ∈ C; reason: any labelling of the components; the statement holds for every choice of roots, as in §6.1
--   - encoding: a_I(G) = E Σ_{Γ connected, V(Γ)=I} Π_{ij∈E(Γ)} (−O_ij), x uniform → activity P F r I: uniform average over x : Comp F → V of the sum over edge sets E ⊆ pairs of distinct elements of I that connect I; reason: definition (6.2); the images of a component are given by the maps that follow P_a from the root
--   - encoding: the hypotheses of Theorem 5.2 (the §6 setting) on G → the same hypotheses on the single core P; G′ does not occur; reason: Lemma 6.1 concerns one core
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 25 (PDF 28), Lemma 6.1

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_PermCores
import Definitions.Def_AcycTesting_NearLinear_Forests

namespace AcycTesting.NearLinear

/-- Lemma 6.1 (tree bound for the activities), under the hypotheses of Theorem 5.2 on one
core `G`: for `m = |I| ≥ 2`, `|a_I(G)| ≤ m^{m-2} (S²/N)^{m-1}`, for every choice of roots. -/
theorem lemma_6_1 {U V : Type*} [Fintype U] [Fintype V] (K Λ : ℕ) (hK : 1 ≤ K) (hΛ : 1 ≤ Λ)
    (N : ℕ) (hN : 0 < N) (hV : Fintype.card V = N) (P : CoreMaps V) (hP : IsPermCore P)
    (hgirth : CoreGirthGT P (2 * K * Λ + 1))
    (F : ColGraph U) (hprop : IsProperCol F) (hfor : IsColForest F) (c : ℕ) (S : ℝ)
    (hc : numComponents F = c) (hS : ComponentsBounded F S Λ)
    (hκ : (c : ℝ) * S ^ 2 / N ≤ 1 / (16 * Real.exp 1 ^ 2))
    (r : Comp F → U) (hr : ∀ C, (weakGraph F).connectedComponentMk (r C) = C)
    (I : Finset (Comp F)) (hI : 2 ≤ I.card) :
    |activity P F r I| ≤ (I.card : ℝ) ^ (I.card - 2) * (S ^ 2 / N) ^ (I.card - 1) := by sorry

end AcycTesting.NearLinear
