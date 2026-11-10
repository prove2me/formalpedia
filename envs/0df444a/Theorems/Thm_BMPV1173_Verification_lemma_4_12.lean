-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_4_12
-- name    : BMPV1173.Verification.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:08:01.056273+00:00
-- url     : https://prove2.me/theorems/c8624203-5697-44c6-b018-37b98cb862ad
-- title:
--   Lemma 4.12 — membership, estimation, coherent setup and update
-- statement:
--   Under the source good events, membership in the implicit class $V_a$ costs $\widetilde O(\sqrt{n(s+n/t)})$ queries. Distinguishing an empty class and otherwise estimating $n_a=|V_a|$ within a factor of two costs $\widetilde O(n\sqrt{s+n/t})$. For a nonempty class and $1\le r\le n_a/2$, the coherent setup and replacement costs are
--   $$S=\widetilde O\!\left(r\sqrt{na}+rn\sqrt{(s+n/t)/n_a}\right),\qquad U=\widetilde O\!\left(\sqrt{na}+n\sqrt{(s+n/t)/n_a}\right).$$
--   Here $na$ means $n\cdot a$; $n_a$ means class cardinality. Setup prepares a uniform $r$-subset with its computed maintained data. Replacement includes coherent selection from the actual implicit class and replacing the maintained data. A known factor-two size estimate may be supplied after the estimation task; the exact unknown class is never supplied. All operations attain any specified inverse-polynomial accuracy.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - encoding: query cost for loading, checking or class access with acquired data free → existence of an actual XOR circuit realizing the specified data task uniformly over every input compatible with the acquired data; reason: the source routines leave their quantum search implementations unspecified; the task contract fixes their complete output and resource behavior without postulating correctness or budgets
--   - encoding: coherent setup and walk update → clean norm approximation on arbitrary admissible superpositions, including sampled data and a reset scratch register; reason: this states the coherent operations required by the source error convention, including implicit member selection
--   - encoding: one coherent replacement in the implicit Johnson walk → uniform neighboring-subset preparation together with the neighboring-data swap, with their summed cost bounded by the stated U expression; reason: this exposes and charges implicit class selection as well as data replacement; inversion has the same query count
--   - encoding: arbitrarily high inverse-polynomial subroutine accuracy → error at most (n+1)^(-c) for every requested c>0; reason: this is nontrivial also at n=1 and supplies the source inverse-polynomial accuracy on all larger positive dimensions
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 4.12, printed p.32 = PDF p.32.

import Definitions.Def_BMPV1173_Verification_Access

namespace BMPV1173.Verification

open scoped BigOperators

/-- All implicit-class operations, Lemma 4.12, p.32. Setup and replacement
are clean coherent operations on the actual implicit class, including the cost
of finding class members. The estimate h is known, while n_a is not. -/
theorem lemma_4_12 (c : ℝ) (hc : 0 < c) (cD cK : ℕ)
    (hcD : 0 < cD) (hcK : 0 < cK) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ (n s t a : ℕ),
      1 ≤ n → 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n → 2*t ≤ a → a ≤ 4*n →
      (∃ b : ℕ, a = 2^b) →
      ∀ (p : Fin s → Fin n) (g : Fin (sampleCount cD n t) → Fin n)
        (v : SampleValues n s (sampleCount cD n t))
        (K : Fin (sampleCount cK n t) → Fin n),
      (∀ i : Fin n, ∃ T : ℕ,
        HasFunction (goodInputs p g v s t K)
          (fun x => by classical exact decide (i ∈ sizeClass (left x p g t) t K a))
          (((n : ℝ)+1)^(-c)) T ∧
        (T : ℝ) ≤ C*Real.sqrt ((n : ℝ)*(s+(n : ℝ)/t))*(1+Real.log (n : ℝ))^k) ∧
      (∃ T : ℕ,
        HasRelation (goodInputs p g v s t K)
          (fun x h => (h = 0 ↔ (sizeClass (left x p g t) t K a).card = 0) ∧
            ((sizeClass (left x p g t) t K a).card ≠ 0 →
              (sizeClass (left x p g t) t K a).card ≤ 2*h ∧
              h ≤ 2*(sizeClass (left x p g t) t K a).card))
          (((n : ℝ)+1)^(-c)) T ∧
        (T : ℝ) ≤ C*(n : ℝ)*Real.sqrt (s+(n : ℝ)/t)*(1+Real.log (n : ℝ))^k) ∧
      ∀ (h r : ℕ), 1 ≤ h → 1 ≤ r →
        let D := {x | x ∈ goodInputs p g v s t K ∧
          (sizeClass (left x p g t) t K a).card ≤ 2*h ∧
          h ≤ 2*(sizeClass (left x p g t) t K a).card ∧
          2*r ≤ (sizeClass (left x p g t) t K a).card}
        ∀ q0 : MatrixIndex n,
        ∃ S U V : ℕ,
          HasCoherentMap q0 D (fun _ (_ : Unit) => True)
            (fun _ _ => QAlgorithms.ket (∅,∅,(fun _ => none : SubsetData n s (sampleCount cD n t))))
            (fun x _ => classSetup x p g t K a r) (((n : ℝ)+1)^(-c)) S ∧
          HasCoherentMap q0 D
            (fun x (I : Finset (Fin n)) => I ∈ classSubsets x p g t K a r)
            (fun x I => QAlgorithms.ket (I,I,subsetData x p g t I))
            (fun x I => classNeighbor x p g t K a r I) (((n : ℝ)+1)^(-c)) U ∧
          HasCoherentMap q0 D
            (fun x (IJ : Finset (Fin n) × Finset (Fin n)) =>
              IJ.1 ∈ classSubsets x p g t K a r ∧ IJ.2 ∈ classSubsets x p g t K a r ∧
              johnsonAdjacent r IJ.1 IJ.2)
            (fun x IJ => QAlgorithms.ket (IJ.1,IJ.2,subsetData x p g t IJ.1))
            (fun x IJ => QAlgorithms.ket (IJ.2,IJ.1,subsetData x p g t IJ.2))
            (((n : ℝ)+1)^(-c)) V ∧
          ∀ x ∈ D,
            let na := ((sizeClass (left x p g t) t K a).card : ℝ)
            (S : ℝ) ≤ C*((r : ℝ)*Real.sqrt ((n : ℝ)*a)+
              r*n*Real.sqrt ((s+(n : ℝ)/t)/na))*(1+Real.log (n : ℝ))^k ∧
            (U : ℝ)+(V : ℝ) ≤ C*(Real.sqrt ((n : ℝ)*a)+
              n*Real.sqrt ((s+(n : ℝ)/t)/na))*(1+Real.log (n : ℝ))^k := by sorry

end BMPV1173.Verification
