-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_5_1
-- name    : AvgValueAlloc.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:41:28.992737+00:00
-- url     : https://prove2.me/theorems/bb59d9b5-f9fa-4bcc-810d-657a226edc2c
-- title:
--   Lemma 5.1 — Reduction to identification (12)
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $I$ a nonempty set of $d$ buyers with $a=\min_{j\in I}\rho_j$ and $\rho_j<2a$ on $I$, $k\ge2$, $T\ge8k$, $S\ge0$, and $D_J$ ($J\in I$) the law (11).
--
--   1. Every causal learner that satisfies (1) on every outcome, with all $S$ historical and $T$ live observations, satisfies
--   $$
--   \mathbb E_J\,\mathbb E\,\mathrm{ALG}(D_J)\ \le\ b_*+2aC_T\bigl[1+(k-1)\alpha_{S+T}\bigr],\qquad b_*=\max_{j\in I}\beta_j,\quad C_T=\frac{(T-1)^2}{2T^2},\tag{12}
--   $$
--   with $J$ uniform on $I$ and $\alpha_{S+T}$ the optimal identification success from $S+T$ pure masks.
--   2. For every $J\in I$ some distribution-known causal policy, feasible on every sequence, earns exactly $\beta_J+\nu_Jk(1-1/T)^{T+1}$ under $D_J$, and this is at least $3ak/32$.
--
--   Learning which buyer to fund is as hard as identifying $J$, while a policy that knows $J$ earns order $ak$.
--
--   Differences from the source:
--   - reading: every prefix-feasible learner → every causal learner satisfying (1) on every history, live sequence and randomness; reason: a learner feasible on realized outcomes becomes everywhere feasible, with the same welfare there, by rejecting violating moves
--   - reading: a real distribution-known causal policy earns X → some deterministic causal policy, feasible on every sequence, has expected welfare exactly X; reason: the page's policy (assign sponsors to J, accept eligible negatives at J after the first sponsor) has this exact value
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §5, p.10, eq. (11); §5.1, Lemma 5.1, p.11, eq. (12)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_iidE
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_prefixFeasible
import Definitions.Def_AvgValueAlloc_Policy
import Definitions.Def_AvgValueAlloc_CausalLearner
import Definitions.Def_AvgValueAlloc_famLaw
import Definitions.Def_AvgValueAlloc_alphaId

namespace AvgValueAlloc

open scoped ENNReal

/-- **Lemma 5.1 (Reduction to identification), (12).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §5.1, Lemma 5.1, p.11: "Every prefix-feasible learner, with all
S historical and T live observations available, satisfies E_J E ALG(D_J) ≤ b_* + 2aC_T[1 + (k −
1)α_{S+T}], b_* = max_{j∈I} β_j, C_T = (T − 1)²/(2T²). (12) For every J a real distribution-known
causal policy earns β_J + ν_J k(1 − 1/T)^{T+1} ≥ 3ak/32." Family (11), p.10.

Let `ρ > 0`, `I` a nonempty set of `d` buyers with `a = min_{j∈I} ρ_j` and `ρ_j < 2a` on `I`,
`k ≥ 2`, `T ≥ 8k`, `S ≥ 0`, and `D_J` the law (11) for `J ∈ I`.
1. Every causal learner satisfying (1) on every outcome has
   `(1/d) Σ_{J∈I} E ALG(D_J) ≤ b_* + 2aC_T[1 + (k − 1)α_{S+T}]`, with `b_* = max_{j∈I} β_j`,
   `C_T = (T − 1)²/(2T²)` and `α_{S+T}` the optimal identification success from `S + T` masks.
2. For every `J ∈ I` some deterministic causal policy satisfying (1) on every sequence has expected
   welfare under `D_J` exactly `β_J + ν_J k(1 − 1/T)^{T+1}`, and this is at least `3ak/32`.

**Formalization Note.** `E ALG` includes the `S` historical draws and the learner's randomness;
learners may depend on the family. Values in `ℝ≥0∞`, right sides cast by `ENNReal.ofReal`. -/
theorem lemma_5_1 {n : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (I : Finset (Fin n))
    (hI : I.Nonempty) (hcl : ∀ j ∈ I, ρ j < 2 * famMin ρ I) (k T S : ℕ) (hk : 2 ≤ k)
    (hT : 8 * k ≤ T) :
    (∀ L : CausalLearner n S T, L.Feasible ρ →
      (∑ J ∈ I, L.EALGiid (famLaw ρ I k T J)) / (I.card : ℝ≥0∞) ≤
        ENNReal.ofReal (((I.sup' hI (famBeta ρ I T) : ℚ) : ℝ) +
          2 * (famMin ρ I : ℝ) * (((T : ℝ) - 1) ^ 2 / (2 * (T : ℝ) ^ 2)) *
            (1 + ((k : ℝ) - 1) * alphaId I.card k T (S + T)))) ∧
    ∀ J ∈ I,
      (∃ π : Policy n, (∀ vs : Fin T → Vec n, prefixFeasible ρ vs (π.run vs)) ∧
        iidE (famLaw ρ I k T J) (Fin T) (fun vs => ENNReal.ofReal (welfare vs (π.run vs))) =
          ENNReal.ofReal ((famBeta ρ I T J : ℝ) +
            (famNu ρ I T J : ℝ) * k * (1 - 1 / (T : ℝ)) ^ (T + 1))) ∧
      3 * (famMin ρ I : ℝ) * k / 32 ≤
        (famBeta ρ I T J : ℝ) + (famNu ρ I T J : ℝ) * k * (1 - 1 / (T : ℝ)) ^ (T + 1) := by sorry

end AvgValueAlloc
