-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_3_3
-- name    : AvgValueAlloc.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:39.555208+00:00
-- url     : https://prove2.me/theorems/5d631e8a-e21a-4553-88ee-ce07f18bce1c
-- title:
--   Lemma 3.3 — Same-union transfer
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$ and $U$ a union of $N$ records whose membership bits (information $Y$ or service $Z$) are independent and fair. The output bank $B_g$ has a law $\kappa$ that may depend on the membership. For a group $J$, fix for each candidate bank a canonical optimum $x^*$ of $F^J_U$ and let $w_i(B)=\sum_jv_{ij}x^*_{ij}(B)$ be the union-optimum record rewards.
--
--   1. If, for every record $i$ and every membership with $i\in Z$, moving $i$ into $Y$ multiplies the expectation of the witness test $w_i(B_g)$ by at most $A$, then
--   $$
--   \mathbb E\,F^J_Y(B_g)\le(1+A)\,\mathbb E\,F^J_Z(B_g).
--   $$
--   2. For a sum of group objectives with bank marginals $B^k_g$, it suffices to have the premise separately for each marginal with its own factor $A_k$: $\ \mathbb E\sum_kF^{J_k}_Y(B^k_g)\le\sum_k(1+A_k)\,\mathbb E\,F^{J_k}_Z(B^k_g)$.
--
--   No independence between bank and sample and no joint likelihood of the selector is assumed.
--
--   Differences from the source:
--   - reading: every nonnegative witness test → the union-optimum record rewards w_i(·) of the fixed optimum; reason: these are the tests the proof uses ("The fair bit and domination give E[1{i∈Y} w_i(B_g)] ≤ A E[1{i∈Z} w_i(B_g)]"); requiring the premise only for them is the stronger statement
--   - generalization: a canonical optimum → every choice of union optimum x*; reason: the statement then holds for the canonical one
--   - encoding: relevant output-bank law → a law κ(mb, ·) on a finite set of outputs with bank maps; reason: banks come from finitely many routings; κ may read the whole membership vector
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3.3, Lemma 3.3, p.8

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_edgeLP
import Definitions.Def_AvgValueAlloc_restrictTo

namespace AvgValueAlloc

/-- **Lemma 3.3 (Same-union transfer).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3.3, Lemma 3.3, p.8: "For each candidate bank fix a canonical
optimum on the full union. If adding i multiplies the relevant output-bank law by at most A on
every nonnegative witness test, then EV_Y(B_g) ≤ (1+A)EV_Z(B_g). For a sum of selector objectives it
suffices to have the bound separately for their bank marginals and to apply each factor before
summing." Setting, p.8: "Thus membership bits are independent and fair; contents remain
complementary."

Let `ρ > 0` and `U` a union of `N` records with independent fair membership bits `mb`:
`Y` the records with bit `true`, `Z` the others. The output takes values `b` in a finite set
with law `κ(mb, ·)`. For a group `J` and banks `bank(b) ≥ 0`, fix for every `b` an optimum
`x*(b)` of `F^J_U(bank b)` and let `w_i(b) = Σ_j v_{ij} x*_{ij}(b)`.
1. If for every record `i` and every `mb` with `i ∉ Y`, adding `i` to `Y` gives
   `E_{κ(mb+i)} w_i ≤ A · E_{κ(mb)} w_i`, then `E F^J_Y(bank B_g) ≤ (1 + A) E F^J_Z(bank B_g)`.
2. For finitely many groups `J_k` with bank marginals `bank_k`, optima `x*_k` and factors `A_k`
   each satisfying the premise of 1 for its marginal:
   `E Σ_k F^{J_k}_Y(bank_k B_g) ≤ Σ_k (1 + A_k) E F^{J_k}_Z(bank_k B_g)`.

**Formalization Note.** The witness tests are the union-optimum record rewards `w_i`, the premise
is required only for them, and the optimum `x*` is arbitrary. `κ` may read the whole membership
vector. -/
theorem lemma_3_3 {n N : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (U : Fin N → Vec n)
    {β : Type} [Fintype β] (κ : (Fin N → Bool) → β → ℝ) (hκ0 : ∀ mb b, 0 ≤ κ mb b)
    (hκ1 : ∀ mb, ∑ b, κ mb b = 1) :
    (∀ (J : Finset (Fin n)) (bank : β → Fin n → ℝ), (∀ b, 0 ≤ bank b) →
      ∀ xs : β → Fin N → Fin n → ℝ,
        (∀ b, LPFeasible ρ (effEdge ρ J) U (bank b) (xs b) ∧
          LPValue U (xs b) = Flp ρ J U (bank b)) →
        ∀ A : ℝ,
          (∀ (mb : Fin N → Bool) (i : Fin N), mb i = false →
            ∑ b, κ (Function.update mb i true) b * ∑ j, ((U i j : ℚ≥0) : ℝ) * xs b i j ≤
              A * ∑ b, κ mb b * ∑ j, ((U i j : ℚ≥0) : ℝ) * xs b i j) →
          (∑ mb : Fin N → Bool, ∑ b, κ mb b *
              Flp ρ J (restrictTo U (Finset.univ.filter fun i => mb i = true)) (bank b)) /
              (2 : ℝ) ^ N ≤
            (1 + A) * ((∑ mb : Fin N → Bool, ∑ b, κ mb b *
              Flp ρ J (restrictTo U (Finset.univ.filter fun i => mb i = false)) (bank b)) /
              (2 : ℝ) ^ N)) ∧
    (∀ (K : Type) [Fintype K] (J : K → Finset (Fin n)) (bank : K → β → Fin n → ℝ),
      (∀ k b, 0 ≤ bank k b) →
      ∀ xs : K → β → Fin N → Fin n → ℝ,
        (∀ k b, LPFeasible ρ (effEdge ρ (J k)) U (bank k b) (xs k b) ∧
          LPValue U (xs k b) = Flp ρ (J k) U (bank k b)) →
        ∀ A : K → ℝ,
          (∀ (k : K) (mb : Fin N → Bool) (i : Fin N), mb i = false →
            ∑ b, κ (Function.update mb i true) b * ∑ j, ((U i j : ℚ≥0) : ℝ) * xs k b i j ≤
              A k * ∑ b, κ mb b * ∑ j, ((U i j : ℚ≥0) : ℝ) * xs k b i j) →
          (∑ mb : Fin N → Bool, ∑ b, κ mb b * ∑ k, Flp ρ (J k)
              (restrictTo U (Finset.univ.filter fun i => mb i = true)) (bank k b)) /
              (2 : ℝ) ^ N ≤
            ∑ k, (1 + A k) * ((∑ mb : Fin N → Bool, ∑ b, κ mb b * Flp ρ (J k)
              (restrictTo U (Finset.univ.filter fun i => mb i = false)) (bank k b)) /
              (2 : ℝ) ^ N)) := by sorry

end AvgValueAlloc
