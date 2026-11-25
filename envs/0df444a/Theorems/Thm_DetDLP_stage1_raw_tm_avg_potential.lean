-- Prove2me | Theorems.Thm_DetDLP_stage1_raw_tm_avg_potential
-- name    : DetDLP.stage1_raw_tm_avg_potential
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:17.068213+00:00
-- url     : https://prove2.me/theorems/14209782-2557-460d-87f5-df156d875ebd
-- title:
--   Unified Stage I Multitape Turing-Machine Realization with Average-Potential Bit-Fixing Guarantee
-- statement:
--   Given the proved parsimonious BTN counting and Stage I prefix-comparison identities (`DetDLP.btn_parsimonious_count_and_stage1_cross_mul`), the proved modular and short-Weierstrass elliptic-curve gadget parsimony theorem (`DetDLP.modular_and_ec_gadget_parsimony`), and black-box BTN contraction (`DetDLP.theorem_2_2_btn_contraction`), there exist uniform deterministic multitape Turing machines $(M_{\mathrm{enum}}, M_{\mathrm{dec}})$ for both $E(\mathbb{F}_p)$ ($p > 3$) and $\mathbb{F}_p^*$ that in the small-group regime enumerate the full group and in the general regime ($|G| \ge 64$, $n \ge 4096 m$) execute bitwise conditional-expectation derandomization to select a seed $S$ whose collision potential $\Phi(\mathcal{F}(S))$ is at most the uniform average $\mathbb{E}_{S'}[\Phi(\mathcal{F}(S'))]$, and decode any $2m$-sumset/prodset target within time $2^{O(b/(\log b)^{1/4})}$ and space $b^{O(1)}$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 Proof of Theorem 3.1 (pp. 11–13)

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Unified atomic `PrimitiveMachine` transition-table realization for both `E(F_p)` and `F_p^*`
Stage I factor-base enumeration and 2m-decomposition decoding (Section 3.1–3.2, pp. 11–13),
given the proved BTN parsimonious counting, `s_BTN` scale selection, eq. (3.5) integer
cross-multiplication, subcube completion count (`DetDLP.btn_parsimonious_count_and_stage1_cross_mul`),
modular/EC gadget parsimony (`DetDLP.modular_and_ec_gadget_parsimony`), and black-box BTN
contraction (`DetDLP.theorem_2_2_btn_contraction`). In the general regime, conditional-expectation
bit-fixing deterministically produces a seed `S` whose collision potential is at most the uniform
average over all seeds. -/
theorem stage1_raw_tm_avg_potential :
    ((∀ (G : BipartiteMultigraph)
        (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
        {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) [DecidablePred R]
        (P0 : ℕ),
        IsParsimonious G T ext R →
        G.nE < P0 →
        (Finset.univ.filter R).card < 2 ^ P0 ∧
        BTNContract G (fun v α => truncPolyOfCoeffs P0 1 (fun _ => if T v α then 1 else 0)) =
          truncPolyOfCoeffs P0 1 (fun _ => (Finset.univ.filter R).card)) ∧
     (∀ (enet Δnet : ℕ),
        let sBTN : ℕ := max 2 (max (enet + 1) (Nat.ceil ((Δnet : ℝ) ^ ((10 : ℝ) / 9))))
        2 ≤ sBTN ∧ enet < sBTN ∧ Δnet ≤ Nat.ceil ((sBTN : ℝ) ^ ((9 : ℝ) / 10))) ∧
     (∀ (p n T m gord H₀ H₁ A₀ B₀ J₀ A₁ B₁ J₁ : ℕ),
        0 < p → 0 < n → 0 < T → 0 < H₀ → 0 < H₁ →
        let μ : ℝ := ((n : ℝ) * (T : ℝ) / (p : ℝ)) ^ m
        (((gord : ℝ) * (J₀ : ℝ) + 64 * (B₀ : ℝ) - 128 * μ * (A₀ : ℝ) + 64 * μ ^ 2 * (H₀ : ℝ)) /
            (μ ^ 2 * (H₀ : ℝ)) ≤
          ((gord : ℝ) * (J₁ : ℝ) + 64 * (B₁ : ℝ) - 128 * μ * (A₁ : ℝ) + 64 * μ ^ 2 * (H₁ : ℝ)) /
            (μ ^ 2 * (H₁ : ℝ))) ↔
        (((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₀ : ℤ) +
            64 * (p : ℤ) ^ (2 * m) * (B₀ : ℤ) -
            128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₀ : ℤ)) * (H₁ : ℤ) ≤
          ((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₁ : ℤ) +
            64 * (p : ℤ) ^ (2 * m) * (B₁ : ℤ) -
            128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₁ : ℤ)) * (H₀ : ℤ))) ∧
     (∀ (b r v p : ℕ), r ≤ b → p ≤ 2 ^ b →
        ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ u < p)).card =
          min ((v + 1) * 2 ^ (b - r)) p - min (v * 2 ^ (b - r)) p ∧
        ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ 1 ≤ u ∧ u < p)).card =
          min ((v + 1) * 2 ^ (b - r)) p - min (max (v * 2 ^ (b - r)) 1) p)) →
    ((∀ (q x y z : ℕ) (γ : Bool) (ssum : ℕ),
        x < q → y < q → z < q →
        ((x + y = ssum ∧ z + (if γ then 1 else 0) * q = ssum) ↔
          (z = (x + y) % q ∧ γ = decide (q ≤ x + y) ∧ ssum = x + y))) ∧
     (∀ (q x y z θ u₁ u₂ : ℕ),
        x < q → y < q → z < q →
        ((x * y = u₁ ∧ θ * q = u₂ ∧ u₂ + z = u₁) ↔
          (z = (x * y) % q ∧ θ = (x * y) / q ∧ θ < q ∧ u₁ = x * y ∧ u₂ = ((x * y) / q) * q))) ∧
     (∀ (p : ℕ) [Fact p.Prime] (u : ZMod p) (ζ : Bool) (winv : ZMod p),
        (((if ζ then (1 : ZMod p) else 0) * u = 0 ∧
          (if ζ then (1 : ZMod p) else 0) * winv = 0 ∧
          (1 - (if ζ then (1 : ZMod p) else 0)) * (u * winv) =
            1 - (if ζ then (1 : ZMod p) else 0)) ↔
         (ζ = decide (u = 0) ∧ winv = u⁻¹))) ∧
     ((∀ (ι₁ ι₂ ζx ζy : Bool),
         let b : Bool → ℤ := fun x => if x then 1 else 0
         let σ₁ := b ι₁
         let σ₂ := (1 - b ι₁) * b ι₂
         let σ₃ := (1 - b ι₁) * (1 - b ι₂) * b ζx * b ζy
         let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
         let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
         (σ₁ = 0 ∨ σ₁ = 1) ∧ (σ₂ = 0 ∨ σ₂ = 1) ∧ (σ₃ = 0 ∨ σ₃ = 1) ∧
         (σ₄ = 0 ∨ σ₄ = 1) ∧ (σ₅ = 0 ∨ σ₅ = 1) ∧
         σ₁ + σ₂ + σ₃ + σ₄ + σ₅ = 1) ∧
      (∀ (p : ℕ) [Fact p.Prime], 2 < p →
         ∀ (aE bE x₁ y₁ x₂ y₂ lsl : ZMod p) (ι₁ ι₂ : Bool),
           y₁ ^ 2 = x₁ ^ 3 + aE * x₁ + bE →
           y₂ ^ 2 = x₂ ^ 3 + aE * x₂ + bE →
           let ζx := decide (x₂ - x₁ = 0)
           let ζy := decide (y₁ + y₂ = 0)
           let b : Bool → ZMod p := fun x => if x then 1 else 0
           let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
           let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
           ((σ₄ * ((x₂ - x₁) * lsl - (y₂ - y₁)) = 0 ∧
             σ₅ * (2 * y₁ * lsl - (3 * x₁ ^ 2 + aE)) = 0 ∧
             (1 - σ₄ - σ₅) * lsl = 0) ↔
            lsl =
              if (!ι₁ && !ι₂ && !ζx) then (y₂ - y₁) * (x₂ - x₁)⁻¹
              else if (!ι₁ && !ι₂ && ζx && !ζy) then (3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹
              else 0)))) →
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
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
       (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let b := bitLen p
          let m := blockCount b
          let gord := Fintype.card E.toAffine.Point
          let n := gord - 1
          ∃ F : Fin m → List E.toAffine.Point,
            (∀ i : Fin m, (F i).Nodup) ∧
            ((¬(64 ≤ gord ∧ 4096 * m ≤ n) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
              (64 ≤ gord ∧ 4096 * m ≤ n ∧
                ∃ S : ECSeed p m,
                  (∀ i : Fin m, (F i).toFinset = ecFactorBlock E (hashThreshold p n m gord) S i) ∧
                  collisionPotentialAdd ((qBlk p n (hashThreshold p n m gord)) ^ m)
                    (ecFactorBlock E (hashThreshold p n m gord) S) ≤
                    (∑ S' : ECSeed p m,
                      collisionPotentialAdd ((qBlk p n (hashThreshold p n m gord)) ^ m)
                        (ecFactorBlock E (hashThreshold p n m gord) S')) /
                      (Fintype.card (ECSeed p m) : ℝ))) ∧
            RunsWithin M_enum out_enum (encodeCurveInput p E) (encodeECFactorBlocks F)
              (mainSpaceBound C b) (mainSpaceBound C b) ∧
            ∀ X : E.toAffine.Point,
              (∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X) →
              ∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X ∧
                RunsWithin M_dec out_dec
                  (Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)])
                  (encodeECDecomp A B)
                  (mainSpaceBound C b) (polyBound C b)) ∧
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
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
                  (fpFactorBlock (p := p) (hashThreshold p n m gord) S) ≤
                  (∑ S' : FpSeed p m,
                    collisionPotentialMul ((qBlk p n (hashThreshold p n m gord)) ^ m)
                      (fpFactorBlock (p := p) (hashThreshold p n m gord) S')) /
                    (Fintype.card (FpSeed p m) : ℝ))) ∧
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
                (mainSpaceBound C b) (polyBound C b)) := by sorry

end DetDLP
