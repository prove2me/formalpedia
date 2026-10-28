-- Prove2me | Theorems.Thm_EthierKurtz_kmt_mixture_coupling
-- name    : EthierKurtz.kmt_mixture_coupling
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:37:25.273137+00:00
-- url     : https://prove2.me/theorems/e8e7afe4-c4a5-4634-9b57-8984bc8b0fd0
-- title:
--   KMT couplings are stable under mixtures
-- statement:
--   Let $F_1,G_1,F_2,G_2$ be probability laws on $\mathbb R$ and $0\le p\le1$. Say $(F,G)$ is a KMT pair if there is a probability measure $Q$ on $\mathbb R^{\mathbb N}\times\mathbb R^{\mathbb N}$ with marginals $F^{\otimes\mathbb N}$ and $G^{\otimes\mathbb N}$ and constants $C,K,\lambda>0$ with $Q\big(\max_{1\le k\le n}|S_k-T_k|>C\log n+x\big)<Ke^{-\lambda x}$ for all $n\ge1$, $x>0$ ($S_k,T_k$ the partial sums of the two coordinates). If $(F_1,G_1)$ and $(F_2,G_2)$ are KMT pairs then so is $$\big(pF_1+(1-p)F_2,\;pG_1+(1-p)G_2\big).$$
--
--   Role: lets the parent replace the bounded part of the step law by a Gaussian while keeping the rest of the law fixed (coupled with itself).
-- source:
--   Komlós, Major, Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 2, Lemma 1, p. 37

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz

theorem kmt_mixture_coupling (F1 G1 F2 G2 M1 M2 : Measure ℝ) [IsProbabilityMeasure F1]
    [IsProbabilityMeasure G1] [IsProbabilityMeasure F2] [IsProbabilityMeasure G2]
    [IsProbabilityMeasure M1] [IsProbabilityMeasure M2] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hM1 : M1 = ENNReal.ofReal p • F1 + ENNReal.ofReal (1 - p) • F2)
    (hM2 : M2 = ENNReal.ofReal p • G1 + ENNReal.ofReal (1 - p) • G2)
    (h1 : ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F1) ∧
        Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => G1) ∧
        ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
          ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
            Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
              ENNReal.ofReal (K * Real.exp (-lam * x)))
    (h2 : ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F2) ∧
        Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => G2) ∧
        ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
          ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
            Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
              ENNReal.ofReal (K * Real.exp (-lam * x))) :
    ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => M1) ∧
      Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => M2) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
            |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by sorry

end EthierKurtz
