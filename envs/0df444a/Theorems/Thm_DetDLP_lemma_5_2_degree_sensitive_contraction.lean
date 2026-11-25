-- Prove2me | Theorems.Thm_DetDLP_lemma_5_2_degree_sensitive_contraction
-- name    : DetDLP.lemma_5_2_degree_sensitive_contraction
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T09:29:13.661183+00:00
-- url     : https://prove2.me/theorems/a7a9e99e-0d4d-4d01-babc-845e0256da9d
-- title:
--   Lemma 5.2: Degree-Sensitive Scalar Contraction in Time $T_{\mathrm{old}} 2^{O(\beta/\sqrt{\rho})}$
-- statement:
--   For all positive integer constants $C, c_0$ and any deterministic multitape entry evaluator $E$, there exist a deterministic multitape Turing machine $M$ and a constant $K \in \mathbb{N}$ such that for every $\beta \ge 2$, $T_{\mathrm{old}} \ge 1$, bipartite BTN $(G, T)$ over $\mathcal{B}_{P, \ell'}$ ($1 \le P, \ell' \le C\beta$) with at most $C\beta$ edges, at most $\beta^{c_0}$ vertices, description length $\mathcal{L}$, and local entries computed by $E$ in time $T_{\mathrm{old}}$ and space $(\beta + \mathcal{L})^{c_0}$, setting $\bar{\Delta} = \max\{\Delta_{\max}(G), \lceil \beta^{9/10} \rceil\}$ and $\rho = \max\{1, \lfloor \log_2(\beta / \bar{\Delta}) \rfloor\}$, machine $M$ computes $\mathrm{Contract}(G, T)$ within
--
--   $$\text{time} \le K(\beta + \mathcal{L} + 1)^K \cdot T_{\mathrm{old}} \cdot 2^{K \beta / \sqrt{\rho}}, \qquad \text{space} \le K(\beta + \mathcal{L} + 1)^K.$$
--
--   When applied to the residual $\beta$-edge graph of maximum degree $\Theta(\beta/m)$ in Section 5.3, $\rho = \Theta(\log m) = \Theta(\log\log b)$, yielding the final $2^{O(b/\sqrt{\log\log b})}$ runtime.
--
--   **Formalization Note** When $\bar{\Delta} > \beta$, $\rho$ clamps cleanly to $1$ via `Nat.floor`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 5.2, Lemma 5.2 (p. 20)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem lemma_5_2_degree_sensitive_contraction :
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
                (polyBound K (β + desc.length)) := by sorry

end DetDLP
