-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_lemma_2
-- name    : CapacitatedKMedianFPT.Main.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:13.811043+00:00
-- url     : https://prove2.me/theorems/b0c37a2d-d6ab-4765-ad3a-37e83fa91da1
-- title:
--   Lemma 2 — L contains leaders and radii satisfying (3.2) and (3.3)
-- statement:
--   Let $I$ be as in Claim 1 and let $(O^\star,\varphi^\star)$ be an optimal solution with facilities $o^\star_1,\dots,o^\star_k$, each serving $n_i=|\varphi^{\star-1}(o^\star_i)|\ge1$ clients. Then the list $L$ of Algorithm 1 contains an entry $((\ell_1,\dots,\ell_k),(\tilde r_1,\dots,\tilde r_k))$ with
--   $$\sum_{i=1}^kn_i\,d(o^\star_i,\ell_i)\le(1+2\varepsilon)\mathrm{OPT}\qquad(3.2)$$
--   $$\sum_{i=1}^kn_i\,\tilde r_i\le(1+5\varepsilon)\mathrm{OPT}\qquad(3.3)$$
--   and, moreover, $d(o^\star_i,\ell_i)\le\tilde r_i$ for every $i$.
--
--   The list is computed without knowledge of the optimum; the lemma guarantees that one branch of the enumeration has good leaders, and the extra clause puts $o^\star_i$ in the ball of radius $\tilde r_i$ around $\ell_i$, which the color-coding step uses.
--
--   **Formalization Note** The nonemptiness of the optimal clusters is the paper's standing assumption of §3 (p. 6).
--
--   Differences from the source:
--
--   - generalization: conclusion (3.2) and (3.3) → (3.2), (3.3) and d(o⋆_i, ℓ_i) ≤ r̃_i for every i; reason: the proof's entry has r̃_i = μ_ε(d(o⋆_i, ℓ_i)) ≥ d(o⋆_i, ℓ_i), and p. 9 uses this to place o⋆_i in F_i; dropping the clause gives the printed statement
--   - generalization: the hitting set H of the greedy algorithm, b_s ∈ argmin, one run of Algorithm 1 → every greedy run (any tie-breaking), every choice of nearest clients b_s and every 3-approximate uncapacitated solution (S, φ); reason: the source fixes no tie-breaking; its run is one of those covered
--   - reading: line 3 sets p_c = d(c, φ(c))/Q, undefined when Q = 0 (possible when C and F overlap, e.g. C = F = {a, b}, k = 2, d(a, b) = 1, U_a = 0, U_b = 2: feasible with OPT = 1 but Q = 0) → when Q = 0 the leader candidates are C ∪ {b_s} (H := C) and no greedy run is required; reason: the only completion that keeps every client available as a leader; when Q = 0 every client is an open facility of S, so |C| ≤ k
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 8, Lemma 2 (3.2), (3.3) and proof (r̃_i = μ_ε(d(o⋆_i, ℓ_i))); p. 6, standing assumptions; p. 9, Algorithm 1

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Leaders

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

/-- **Lemma 2** (p. 8). Let `(O⋆, φ⋆)` be an optimal solution with facilities `o⋆_1, …, o⋆_k`, each
serving `n_i ≥ 1` clients. The list `L` of Algorithm 1 contains an entry `(ℓ, r̃)` with
`∑ n_i d(o⋆_i, ℓ_i) ≤ (1+2ε) OPT` (3.2) and `∑ n_i r̃_i ≤ (1+5ε) OPT` (3.3); moreover
`d(o⋆_i, ℓ_i) ≤ r̃_i` for every `i`. -/
theorem lemma_2 {P : Type} [Fintype P] [DecidableEq P] (I : Instance P) (ε : ℝ) (S : Finset P)
    (φ b : P → P) (H : Finset P) (o : Fin I.k → P) (φs : P → P)
    (hI : I.IsValid) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hD : I.HasIntDistancesUpTo (distanceBound I.size ε))
    (hS : I.IsUncapApprox 3 S φ) (hb : I.IsNearestClientChoice S b)
    (hH : I.cost φ ≠ 0 → I.IsGreedyHittingSet (I.ballSystem ε φ) H)
    (hopt : I.IsIndexedOptimum o φs) (hn : ∀ i, 1 ≤ I.load φs (o i)) :
    ∃ e ∈ I.leaderList ε S φ b H,
      ∑ i, (I.load φs (o i) : ℝ) * I.d (o i) (e.1 i) ≤ (1 + 2 * ε) * I.cost φs ∧
      ∑ i, (I.load φs (o i) : ℝ) * (e.2 i : ℝ) ≤ (1 + 5 * ε) * I.cost φs ∧
      ∀ i, I.d (o i) (e.1 i) ≤ (e.2 i : ℝ) := by sorry

end CapacitatedKMedianFPT.Main
