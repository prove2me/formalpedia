-- Prove2me | Theorems.Thm_DetDLP_fp_stage1_btn_derand_tm
-- name    : DetDLP.fp_stage1_btn_derand_tm
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:31.409872+00:00
-- url     : https://prove2.me/theorems/933e3035-52ef-4e79-ad1b-eb36337917f2
-- title:
--   Atomic $\mathbb{F}_p^*$ Stage I BTN Derandomization and Decoding Machine
-- statement:
--   Atomic multitape Turing-machine realization compiling BTN-based conditional-expectation derandomization (Theorem 2.2) to enumerate valid affine-interval factor-base blocks $F_i \subseteq \mathbb{F}_p^*$ and recover 2m-term product decompositions within Stage I time and space bounds.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 7–10)

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Atomic multitape Turing-machine realization for `F_p^*` Stage I enumeration and decoding
(Section 3.1–3.2): compiles the BTN derandomization network (using Theorem 2.2) in the general
regime or full enumeration in the small-group regime, and streams 2m-term decompositions. -/
theorem fp_stage1_btn_derand_tm :
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
          ((¬(64 ≤ gord ∧ 4096 * m ≤ n) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
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
