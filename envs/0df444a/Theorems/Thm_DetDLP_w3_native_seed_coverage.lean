-- Prove2me | Theorems.Thm_DetDLP_w3_native_seed_coverage
-- name    : DetDLP.w3_native_seed_coverage
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:29:22.416049+00:00
-- url     : https://prove2.me/theorems/71c4a684-443f-45b1-b91a-af4437c4c603
-- title:
--   Surjectivity of a native factor base in the large regime
-- statement:
--   In either native group family, the large-instance inequalities ensure the existence of an affine-hash seed whose enumerated blocks are repetition-free and whose two-elements-per-block sum map is onto the whole group. In the prime-field case the additive formulation denotes multiplication in the unit group. In particular, coverage does not require that the reference enumeration retain its originating seed.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_Driver
set_option autoImplicit false
open DetDLP

theorem DetDLP.w3_native_seed_coverage :
    (∀ (p : ℕ) [Fact p.Prime], let M := p-1; let m := blockCount (bitLen p)
      w3_large p M → ∃ (s : FpSeed p m) (B : Fin m → List (ZMod p)ˣ),
        (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (hashThreshold p M m M) s i) ∧
        Function.Surjective (w3_fpFB B).tupleVal) ∧
    (∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      letI := ecPointFintype E; let M := Fintype.card E.toAffine.Point; let m := blockCount (bitLen p)
      w3_large p M → ∃ (s : ECSeed p m) (B : Fin m → List E.toAffine.Point),
        (∀ i, (B i).Nodup ∧ (B i).toFinset = ecFactorBlock E (hashThreshold p (M-1) m M) s i) ∧
        Function.Surjective (IndexedFactorBase.mk B).tupleVal) := by sorry
