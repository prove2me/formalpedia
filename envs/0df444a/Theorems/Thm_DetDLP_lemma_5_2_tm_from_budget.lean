-- Prove2me | Theorems.Thm_DetDLP_lemma_5_2_tm_from_budget
-- name    : DetDLP.lemma_5_2_tm_from_budget
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:44.415802+00:00
-- url     : https://prove2.me/theorems/7aa8725c-e893-40a1-813c-aa203ca144f2
-- title:
--   Deterministic Cauchy–Hermite Contraction Machine from Quantitative Recursion Budget
-- statement:
--   Assuming the quantitative Cauchy–Hermite recursion budget (`DetDLP.cauchy_hermite_recursion_budget`), there exists a deterministic multitape Turing machine contracting any bipartite BTN of at most $C\beta$ edges, at most $\beta^{c_0}$ vertices, max degree $\Delta$, and $(\mathbb{Z}/2^P\mathbb{Z})[W]/(W^{\ell'})$ entries deterministically evaluable in time $T_{\mathrm{old}}$ and space $(\beta + \mathcal{L})^{c_0}$, within $(\beta + \mathcal{L})^{O(1)} T_{\mathrm{old}} 2^{O(\beta/\sqrt{\rho})}$ bit operations and polynomial space.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 5.1–5.2, Proof of Lemma 5.2 (pp. 18–20)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- Machine-realization core of Lemma 5.2 (Degree-Sensitive Scalar Contraction, Section 5.1–5.2,
pp. 18–20): given the quantitative Cauchy–Hermite recursion budget (`cauchy_hermite_recursion_budget`),
any degree-bounded bipartite BTN with entries evaluable in time `T_old` and space `(β + L)^{c_0}`
contracts deterministically in time `(β + L)^{O(1)} T_old 2^{O(β / √ρ)}` and space `(β + L)^{O(1)}`. -/
theorem lemma_5_2_tm_from_budget :
    ((∀ (D : ℕ) (β ρ : ℝ), 0 ≤ β → 0 < ρ →
        ∑ d ∈ Finset.range (D + 1),
          (β * ((1 : ℝ) / 8) ^ d) / Real.sqrt (ρ * ((1 : ℝ) / 2) ^ d) ≤
          (4 / 3 : ℝ) * (β / Real.sqrt ρ)) ∧
      (∀ (D : ℕ) (ε ρ : ℝ), 0 ≤ ε → 0 ≤ ρ →
        2 * (∑ j ∈ Finset.range (D + 1), (Nat.floor (ε * ρ / (2 : ℝ) ^ j) : ℝ)) ≤
          4 * ε * ρ) ∧
      (∀ M : ℕ, 1 ≤ M →
        3 * M / 32 < M / 8 + 1 ∧ (3 : ℝ) * (M : ℝ) / 32 < (M : ℝ) / 8)) →
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            ∃ w : List Bool,
              EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                (polyBound K (β + desc.length)) := by
  sorry

end DetDLP
