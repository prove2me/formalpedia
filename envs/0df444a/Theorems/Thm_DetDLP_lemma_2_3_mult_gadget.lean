-- Prove2me | Theorems.Thm_DetDLP_lemma_2_3_mult_gadget
-- name    : DetDLP.lemma_2_3_mult_gadget
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T09:17:53.450001+00:00
-- url     : https://prove2.me/theorems/60dcc9ed-a16f-4e80-acea-5384d32fe5bd
-- title:
--   Lemma 2.3: Two-Layer Schönhage–Strassen Multiplication Gadget
-- statement:
--   There exist a uniform deterministic multitape Turing machine $E$ and a constant $K \in \mathbb{N}$ such that for every integer $d \ge 1$, the exact unsigned integer multiplication relation
--
--   $$a \cdot b = c_{\mathrm{out}}, \qquad a, b \in [0, 2^d), \quad c_{\mathrm{out}} \in [0, 2^{2d})$$
--
--   admits a parsimonious $\{0, 1\}$-valued bipartite Boolean tensor network $(G, T)$ on $4d$ interface edges satisfying $|E(G)| < 1100(d + 1)$, $\Delta_{\max}(G) < 136(d + 1)^{3/4}$, $|V(G)| \le K(d + 1)^K$, and local entry evaluation by $E$ in time and space at most $K(d + 1)^K$.
--
--   This low-degree linear-edge multiplication gadget is the core building block for all modular arithmetic, elliptic-curve group law, factoring, and Stage I/II separator networks.
--
--   **Formalization Note** Interface integers are decoded little-endian via `bitsToNat` across disjoint slices of `Fin (4 * d)` mapped injectively into `Fin G.nE`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem lemma_2_3_mult_gadget :
    ∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
      ∀ d : ℕ, 1 ≤ d →
        ∃ (G : BipartiteMultigraph)
          (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
          (ext : Fin (4 * d) → Fin G.nE),
          G.nE < 1100 * (d + 1) ∧
          (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
          (G.nV : ℝ) ≤ polyBound K d ∧
          BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
          IsParsimonious G T ext (fun x =>
            bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
            bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
            bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)) := by sorry

end DetDLP
