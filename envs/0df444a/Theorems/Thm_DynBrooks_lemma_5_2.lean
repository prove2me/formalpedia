-- Prove2me | Theorems.Thm_DynBrooks_lemma_5_2
-- name    : DynBrooks.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:04.488878+00:00
-- url     : https://prove2.me/theorems/8ab4155c-6520-4d0b-a774-9b794e919400
-- title:
--   Lemma 5.2 — forward-choice bounds of a repair attempt
-- statement:
--   Fix a graph $G$ on $[n]$ of maximum degree at most $\Delta\ge16$ with no $K_{\Delta+1}$, a proper partial coloring $\chi_0$ with exactly one hole $v_0$, and a stored neighbor array, and run Algorithm 3. Write $a_i$ for the number of choices for the next vertex at arrival $i$, $s_i=|N[v_i]\setminus N[v_{i-1}]|$ and $b_i=|N(v_i)\cap X_{i-1}|-1$. Then:
--
--   1. at every continuing arrival $i\ge1$, $a_i=s_i-b_i\ge1$;
--   2. at a collision, $a_i=\Delta-2$;
--   3. if $i$ and $i+1$ are consecutive continuing arrivals and neither is a collision, then $a_ia_{i+1}\ge\Delta-1$;
--   4. two collisions in a continuing path are separated by at least four positions.
--
--   A continuing arrival is one the attempt can reach and at which the stopping tests 1–4 fail. These bounds are the per-path probability estimates of the counting argument in §5.2.
--
--   Differences from the source:
--   - generalization: the stored neighbor array of the data structure → every neighbor array (each neighbor listed once, in any order); reason: the paper's array is one of them
--   - reading: test 4: 'v_i has two neighbors in X_{i−1}' → at least two neighbors in X_{i−1}; reason: with three or more earlier neighbors test 2 already succeeds (p.62), so the two readings stop at the same arrivals
--   - encoding: the path v₀, …, v_i and the arrival at position j → the list [v_i, …, v₀]; the arrival at position j of a path q is its suffix of length j + 1; reason: a representation of the same paths
--   - encoding: a continuing arrival of an attempt with length limit L → an arrival the attempt can reach with no length limit and at which tests 1–4 fail (Continuing); reason: the test i = L only cuts the path off, so an arrival that continues under some L > i is exactly this; every L is covered
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 5.2, p.57 (PDF 59); standing assumptions §5, p.54 (PDF 56)

import Mathlib
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynBrooks_Attempt

namespace DynBrooks

/-- **Lemma 5.2** (Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*, STOC 2027 submission,
sha256 6542a9f1…, p.57 (PDF 59)), under the standing assumptions of §5, p.54: a graph of maximum
degree at most `∆ ≥ 16` with no `K_{∆+1}` and a proper partial coloring `χ₀` with one hole `v₀`.
At every continuing arrival `i ≥ 1`, `a_i = s_i − b_i ≥ 1`. At a collision, `a_i = ∆ − 2`. If `i` and
`i + 1` are consecutive continuing arrivals and neither is a collision, then `a_i a_{i+1} ≥ ∆ − 1`.
Two collisions in a continuing path are separated by at least four positions.

**Formalization Note.** A path `v₀, …, v_i` is the list `[v_i, …, v₀]`, so arrival `i ≥ 1` means
`2 ≤ p.length`, and the arrival at position `j` of a path `q` is the suffix `q.drop (q.length − 1 − j)`.
A continuing arrival is one that Algorithm 3 can reach and at which tests 1–4 fail (`Continuing`);
`a_i = numChoices`, `s_i = sIdx`, `b_i = bIdx`. The statement holds for every stored neighbor array. -/
theorem lemma_5_2 (n Δ : ℕ) (hΔ : 16 ≤ Δ) (G : SimpleGraph (Fin n)) (hG : IsBrooks Δ G)
    (χ₀ : Fin n → ℕ) (hχ : IsPartialColoring Δ G χ₀) (v₀ : Fin n) (hv₀ : HasOneHole χ₀ v₀)
    (nbr : Fin n → List (Fin n)) (hnbr : IsNeighborArray G nbr) :
    (∀ p : List (Fin n), Continuing Δ G χ₀ nbr v₀ p → 2 ≤ p.length →
        (numChoices G p : ℤ) = (sIdx G p : ℤ) - bIdx G p ∧ 1 ≤ numChoices G p) ∧
    (∀ p : List (Fin n), Continuing Δ G χ₀ nbr v₀ p → IsCollision G p →
        numChoices G p = Δ - 2) ∧
    (∀ (x : Fin n) (p : List (Fin n)), Continuing Δ G χ₀ nbr v₀ p →
        Continuing Δ G χ₀ nbr v₀ (x :: p) → 2 ≤ p.length →
        ¬ IsCollision G p → ¬ IsCollision G (x :: p) →
        Δ - 1 ≤ numChoices G p * numChoices G (x :: p)) ∧
    (∀ q : List (Fin n), Continuing Δ G χ₀ nbr v₀ q → ∀ i j : ℕ, i < j → j < q.length →
        IsCollision G (q.drop i) → IsCollision G (q.drop j) → 4 ≤ j - i) := by sorry

end DynBrooks
