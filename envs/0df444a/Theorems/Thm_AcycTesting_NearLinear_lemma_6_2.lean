-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_6_2
-- name    : AcycTesting.NearLinear.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:48.064916+00:00
-- url     : https://prove2.me/theorems/ede417a0-d4d4-4ba3-bb06-8f993bf62b2a
-- title:
--   Lemma 6.2 — universality: activities of at most K components agree in any two cores of weak girth > 2KΛ + 1
-- statement:
--   Under the hypotheses of Theorem 5.2 (integers $K,\Lambda\ge1$; permutation cores $G,G'$ on $N\ge1$ vertices with weak girth greater than $2K\Lambda+1$; a proper coloured forest $F$ with $c$ components, each with at most $S$ vertices and weak diameter at most $\Lambda$; $\kappa=cS^2/N\le1/(16e^2)$), and for every choice of roots,
--   $$a_I(G)=a_I(G')\qquad\text{whenever } 2\le|I|\le K.$$
--   Only overlap patterns of more than $K$ components can distinguish two high-girth cores.
--
--   Differences from the source:
--   - encoding: G, G′ permutation cores on N vertices → P : CoreMaps V, P′ : CoreMaps V′ on Fintypes with card N (possibly different types), each map bijective; reason: an N-vertex core on any N-set; the statement is invariant under relabelling
--   - encoding: κ = cS²/N, N vertices → 0 < N assumed; reason: κ is undefined at N = 0; this excludes only the undefined case
--   - encoding: F with c components, each with at most S vertices and weak diameter at most Λ → numComponents F = c (weak components of the underlying graph), ComponentsBounded F S Λ with S real; reason: the source's S need not be an integer (S = N^z in Theorem 5.1)
--   - encoding: components F1, …, Fc indexed by [c], fixed roots r_i → components indexed by Mathlib ConnectedComponent of the underlying graph; an arbitrary root function r with r C ∈ C; reason: any labelling of the components; the statement holds for every choice of roots, as in §6.1
--   - encoding: a_I(G) = E Σ_{Γ connected, V(Γ)=I} Π_{ij∈E(Γ)} (−O_ij), x uniform → activity P F r I: uniform average over x : Comp F → V of the sum over edge sets E ⊆ pairs of distinct elements of I that connect I; reason: definition (6.2); the images of a component are given by the maps that follow P_a from the root
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 25 (PDF 28), Lemma 6.2

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_PermCores
import Definitions.Def_AcycTesting_NearLinear_Forests

namespace AcycTesting.NearLinear

/-- Lemma 6.2 (universality of local counts): under the hypotheses of Theorem 5.2,
`a_I(G) = a_I(G')` whenever `2 ≤ |I| ≤ K`, for every choice of roots. -/
theorem lemma_6_2 {U V V' : Type*} [Fintype U] [Fintype V] [Fintype V'] (K Λ : ℕ)
    (hK : 1 ≤ K) (hΛ : 1 ≤ Λ) (N : ℕ) (hN : 0 < N)
    (hV : Fintype.card V = N) (hV' : Fintype.card V' = N)
    (P : CoreMaps V) (P' : CoreMaps V') (hP : IsPermCore P) (hP' : IsPermCore P')
    (hgirth : CoreGirthGT P (2 * K * Λ + 1)) (hgirth' : CoreGirthGT P' (2 * K * Λ + 1))
    (F : ColGraph U) (hprop : IsProperCol F) (hfor : IsColForest F) (c : ℕ) (S : ℝ)
    (hc : numComponents F = c) (hS : ComponentsBounded F S Λ)
    (hκ : (c : ℝ) * S ^ 2 / N ≤ 1 / (16 * Real.exp 1 ^ 2))
    (r : Comp F → U) (hr : ∀ C, (weakGraph F).connectedComponentMk (r C) = C)
    (I : Finset (Comp F)) (hI : 2 ≤ I.card) (hIK : I.card ≤ K) :
    activity P F r I = activity P' F r I := by sorry

end AcycTesting.NearLinear
