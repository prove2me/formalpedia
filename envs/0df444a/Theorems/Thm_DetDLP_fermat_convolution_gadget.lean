-- Prove2me | Theorems.Thm_DetDLP_fermat_convolution_gadget
-- name    : DetDLP.fermat_convolution_gadget
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:47:36.084574+00:00
-- url     : https://prove2.me/theorems/1ecdcfbd-ccb6-498d-b166-9e02e2b73b3d
-- title:
--   Two-layer Fermat-ring convolution network with a carry check
-- statement:
--   For each unsigned operand width d, there are a positive limb width k and limb count L with d≤kL and L≤2ᵏ, together with a parsimonious bipartite Boolean tensor network. On two d-bit words the interface relation forms their base-2ᵏ limbs and their ordinary zero-padded convolution, reduces each coefficient modulo 2⁴ᵏ+1, and checks that the base-2ᵏ weighted sum of these residues equals the 2d-bit output word. The edge, degree, vertex-count and uniform local-evaluation bounds are precisely those of Lemma 2.3. This isolates the two-layer transform, wiring, and carry predicates from the arithmetic proof that the accepted interface words encode an exact integer product.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Lemma 2.3, Section 2.3.

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem fermat_convolution_gadget :
    ∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
      ∀ d : ℕ, 1 ≤ d →
        ∃ (k L : ℕ), 0 < k ∧ d ≤ k*L ∧ L ≤ 2^k ∧
        ∃ (G : BipartiteMultigraph)
          (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
          (ext : Fin (4 * d) → Fin G.nE),
          G.nE < 1100 * (d + 1) ∧
          (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
          (G.nV : ℝ) ≤ polyBound K d ∧
          BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
          IsParsimonious G T ext (fun x =>
            let a := bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩)
            let b := bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩)
            let cout := bitsToNat (fun i : Fin (2*d) => x ⟨2*d+i.val, by omega⟩)
            let B := 2^k
            let Q := 2^(4*k)+1
            let limb (w i : ℕ) := w / B^i % B
            let c (u : ℕ) := ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
              if i+j=u then limb a i * limb b j else 0
            (∑ u ∈ Finset.range (2*L), (c u % Q)*B^u) = cout) := by sorry

end DetDLP
