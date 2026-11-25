-- Prove2me | Theorems.Thm_DetDLP_fp_stage1_tm_from_seed_witness
-- name    : DetDLP.fp_stage1_tm_from_seed_witness
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:49:56.27628+00:00
-- url     : https://prove2.me/theorems/56895197-08d0-4c49-a8ec-6abf3aa56d2c
-- title:
--   Prime-Field Stage I Conditional-Expectation and Prefix-Pinning Machine Realization
-- statement:
--   Assuming black-box Boolean tensor network contraction (Theorem 2.2) and the existence in the general regime ($p - 1 \ge \max(64, 4096 m)$) of an affine-interval seed $S \in \mathrm{FpSeed}(p, m)$ with collision potential $\Phi(S) \le 373/336$ (supplied by Lemma 3.2), there exist uniform deterministic multitape Turing machines $(M_{\mathrm{enum}}, M_{\mathrm{dec}})$ realizing Stage I for $\mathbb{F}_p^*$: outputting nodup factor-base lists $F_1, \dots, F_m$ of total size $O(m^2 + m(p-1)^{1/m})$ (either $F_i = \mathbb{F}_p^*$ in the small-group regime or $F_i = F_i(S)$ for a derandomized seed with $\Phi(S) \le 373/336$) and deterministically finding a $2m$-term product decomposition for any representable target $X \in \mathbb{F}_p^*$ within the Stage I time and space bounds.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Proof of Theorem 3.1 (pp. 11–14)

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Prime-field multiplicative Stage I Turing-machine realization (Section 3.1–3.2):
assuming black-box BTN contraction (Theorem 2.2) and the existence of a good affine-interval seed
with collision potential `≤ 373/336` in the general regime (supplied by Lemma 3.2), there exist
deterministic multitape machines `(M_enum, out_enum, M_dec, out_dec, C)` that for every prime `p`
enumerate nodup factor-base lists `F : Fin m → List (ZMod p)ˣ` satisfying the size bound (either
`F_i = F_p^*` in the small-group regime or a derandomized seed `S` with `Φ(S) ≤ 373/336` in the
general regime) and, for any target `X ∈ F_p^*` admitting a 2m-term product decomposition in `F`,
deterministically recover one within the Stage I time and space bounds. -/
theorem fp_stage1_tm_from_seed_witness :
    (∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s → G.nE ≤ C * s → G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s → 1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length))) →
    (∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let μ := (qBlk p n T) ^ m
      ∃ S : FpSeed p m, collisionPotentialMul μ (fpFactorBlock (p := p) T S) ≤ (373 : ℝ) / 336) →
    ∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
      (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        let gord := p - 1
        let n := p - 1
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ i : Fin m, (F i).Nodup) ∧
          ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
            (C : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) ∧
          ((∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
            (64 ≤ gord ∧ 4096 * m ≤ n ∧
              ∃ S : FpSeed p m,
                (∀ i : Fin m, (F i).toFinset = fpFactorBlock (p := p) (hashThreshold p n m gord) S i) ∧
                collisionPotentialMul ((qBlk p n (hashThreshold p n m gord)) ^ m)
                  (fpFactorBlock (p := p) (hashThreshold p n m gord) S) ≤ (373 : ℝ) / 336)) ∧
          RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound C b) (mainSpaceBound C b) ∧
          ∀ X : (ZMod p)ˣ,
            (∃ A B : Fin m → (ZMod p)ˣ,
              (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
              (∏ i : Fin m, (A i * B i)) = X) →
            ∃ A B : Fin m → (ZMod p)ˣ,
              (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
              (∏ i : Fin m, (A i * B i)) = X ∧
              RunsWithin M_dec out_dec
                (encodeNatListBin [p, (X : ZMod p).val])
                (encodeFpDecomp A B)
                (mainSpaceBound C b) (polyBound C b) := by sorry

end DetDLP
