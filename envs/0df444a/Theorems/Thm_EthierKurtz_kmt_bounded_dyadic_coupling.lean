-- Prove2me | Theorems.Thm_EthierKurtz_kmt_bounded_dyadic_coupling
-- name    : EthierKurtz.kmt_bounded_dyadic_coupling
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:26:28.560397+00:00
-- url     : https://prove2.me/theorems/a4ad36a1-4a59-46a2-9872-14930d75e7ac
-- title:
--   KMT theorem for bounded laws on dyadic horizons
-- statement:
--   Let $F$ be a probability law on $\mathbb R$ with $|x|\le K$ $F$-a.s. ($K>0$), $\int x\,dF=0$ and $\int x^2\,dF=1$. Then there are constants $C,K,\lambda>0$ such that for every $N$ there is a coupling $Q_N$ of $F^{\otimes 2^N}$ and $N(0,1)^{\otimes 2^N}$ on $\mathbb R^{2^N}\times\mathbb R^{2^N}$ with $$Q_N\Big(\max_{1\le k\le 2^N}|S_k-T_k|>C\log 2^N+x\Big)<Ke^{-\lambda x}\qquad(x>0)$$.
--
--   Role: the bounded case (Theorem 1B) of the KMT theorem, used for the bounded part of the step law.
-- source:
--   Komlós, Major, Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 4, Theorem 1B, pp. 41-51

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz

theorem kmt_bounded_dyadic_coupling (F : Measure ℝ) [IsProbabilityMeasure F] (K : ℝ) (hK : 0 < K)
    (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => F) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by sorry

end EthierKurtz
