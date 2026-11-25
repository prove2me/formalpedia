-- Prove2me | Theorems.Thm_DetDLP_theorem_2_2_btn_contraction
-- name    : DetDLP.theorem_2_2_btn_contraction
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T09:17:19.21486+00:00
-- url     : https://prove2.me/theorems/3af04e0c-8054-4476-8975-3179520d57bd
-- title:
--   Theorem 2.2: Deterministic Boolean Tensor Contraction over $\mathcal{B}_{P_0,\ell}$
-- statement:
--   For any fixed positive integer constants $C, A, c_0$ and any uniform deterministic multitape Turing machine $E$ evaluating local tensor entries, there exist a deterministic multitape Turing machine $M$ and a constant $K \in \mathbb{N}$ such that for every integer $s \ge 2$, every description bitstring $\mathrm{desc}$ of length $\mathcal{L}$, every bipartite multigraph $G$ with at most $Cs$ edges, at most $s^{c_0}$ vertices, and maximum degree at most $\lceil s^{9/10} \rceil$, every $1 \le P_0, \ell \le Cs$, and every family of local tensors over $\mathcal{B}_{P_0, \ell} = (\mathbb{Z}/2^{P_0}\mathbb{Z})[z]/(z^\ell)$ whose entries are computed by $E$ in time $(s + \mathcal{L})^{c_0} 2^{A s^{9/10}}$ and space $(s + \mathcal{L})^{c_0}$, machine $M$ outputs the canonical encoding of $\mathrm{Contract}(G, T)$ within
--
--   $$\text{time} \le K(s + \mathcal{L} + 1)^K \cdot 2^{K s / \sqrt{\log_{\mathrm{safe}} s}}, \qquad \text{space} \le K(s + \mathcal{L} + 1)^K.$$
--
--   This black-box contraction theorem is the foundational algorithmic engine underlying Stage I factor-base derandomization, integer factorization, and primitive-root construction.
--
--   **Formalization Note** Stated unconditionally on `PrimitiveMachine` using `TruncPoly P0 ℓ` and canonical binary encodings from `Def_DetDLP_BTN`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.2, Theorem 2.2 (pp. 7–8), citing OpenAI (Oct 25, 2026), Theorem D.1

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem theorem_2_2_btn_contraction :
    ∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s →
            G.nE ≤ C * s →
            G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s →
            1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length)) := by sorry

end DetDLP
