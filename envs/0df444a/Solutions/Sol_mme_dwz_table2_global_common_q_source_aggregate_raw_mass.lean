-- Prove2me | solution 1 for mme_dwz_table2_global_common_q_source_aggregate_raw_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T09:41:08.966979+00:00
-- url     : https://prove2.me/submissions/a6932574-11b6-4979-b604-a111a49afb01

import Theorems.Thm_mme_dwz_table2_global_common_q_aggregate_counting_capstone
import Theorems.Thm_mme_dwz_common_state_shared_tensor

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

/-! Public-only two-child proof sketch for raw source leaf `71c271fb...`. -/

theorem solution {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      ∃ (n p N fixedTargetCard d Q : ℕ)
          (R : ℝ) (S : Finset ℕ)
          (reindex : Fin (N + 1) ≃ Fin L)
          (q : (Fin (N + 2) → ZMod p) × ZMod p)
          (edge : Fin n → Fin (N + 1) → Fin 15),
        0 < m ∧
        2 ≤ p ∧
        Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
            Nat.multinomial Finset.univ
                (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
              fixedTargetCard ∧
        0 < d ∧
        (d : ℝ) ≤
          (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
            (((L + 1 : ℕ) : ℝ)) ^ 15 *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                (MME.DWZSquare.maxSameMarginalEntropy -
                  mme_modern_entropyBits
                    (mme_modern_marginal MME.DWZSquare.shapeX
                      MME.DWZSquare.alpha))) ∧
        R =
          (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
            (fixedTargetCard : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ∧
        (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
        d ≤ 15 ^ L ∧
        Q ≤ 15 ^ L ∧
        p ≤ 2 * max 4 (8 * max d Q) ∧
        ((p / 2 : ℕ) : ℝ) *
              Real.exp (-4 * Real.sqrt
                (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
            (S.card : ℝ) ∧
        (∀ r s,
          Fintype.card
              {t : Fin L //
                MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun r ↦
            MME.DWZSourceAligned.brokenAddressObj K m
              (MME.DWZGlobalCorrelated.sourceWord reindex edge r)
              (MME.DWZGlobalCorrelated.commonStateBrokenCopy
                m reindex q edge r)))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L) ∧
        ((Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) : ℝ) *
            (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ r, MME.DWZSquare.nonholeFraction
            (MME.DWZGlobalCorrelated.commonStateBrokenCopy
              m reindex q edge r) := by
  filter_upwards
    [mme_dwz_table2_global_common_q_aggregate_counting_capstone] with m h
  dsimp only at h ⊢
  rcases h with
    ⟨n, p, fixedTargetCard, d, Q, R, S, _base, reindex, q, A, _I,
      edge, hm, hp2, hpPrime, hpOdd, _hp4, _hbase, _hfixed,
      hfactor, hdpos, hdRate, hR, hpReal, hdPow, hQPow, hpUpper,
      hSrange, hSfree, hBehrend, _hA, _hIExact, _hIBucket, _hIsolated,
      _hIcard, hedgeInjective, _hImage, hedgeBucket, hedgeProfile,
      hXYOwner, hMass⟩
  let L : ℕ := MME.DWZTable2Counts.scale * m
  let N : ℕ := L - 1
  let : Fact p.Prime := ⟨hpPrime⟩
  have hRestrict := mme_dwz_common_state_shared_tensor
    (K := K) (m := m) (n := n) (p := p) (N := N) (L := L)
      hpOdd S hSrange hSfree A q reindex edge hedgeInjective
        hedgeBucket hedgeProfile hXYOwner
  refine ⟨n, p, N, fixedTargetCard, d, Q, R, S, reindex, q, edge,
    hm, hp2, hfactor, hdpos, hdRate, hR, hpReal, hdPow, hQPow,
    hpUpper, hBehrend, hedgeProfile, ?_, hMass⟩
  simpa only [L, N] using hRestrict
