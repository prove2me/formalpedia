-- Prove2me | Theorems.Thm_EthierKurtz_kmt_dyadic_blocks_glue
-- name    : EthierKurtz.kmt_dyadic_blocks_glue
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:31:59.015786+00:00
-- url     : https://prove2.me/theorems/604939c3-9106-429f-95cb-669a5916d713
-- title:
--   Dyadic finite-horizon KMT couplings glue to an infinite one
-- statement:
--   Let $F$ be a probability law on $\mathbb R$. Suppose there are constants $C,K,\lambda>0$ such that for every $N$ there is a coupling $Q_N$ of $F^{\otimes 2^N}$ and $N(0,1)^{\otimes 2^N}$ on $\mathbb R^{2^N}\times\mathbb R^{2^N}$ with $$Q_N\Big(\max_{1\le k\le 2^N}|S_k-T_k|>C\log 2^N+x\Big)<Ke^{-\lambda x}\qquad(x>0)$$ ($S_k,T_k$ the partial sums of the first $k$ coordinates). Then there is a probability measure $Q$ on $\mathbb R^{\mathbb N}\times\mathbb R^{\mathbb N}$ with marginals $F^{\otimes\mathbb N}$ and $N(0,1)^{\otimes\mathbb N}$ and constants $C,K,\lambda>0$ with $Q\big(\max_{1\le k\le n}|S_k-T_k|>C\log n+x\big)<Ke^{-\lambda x}$ for all $n\ge1$, $x>0$ ($S_k,T_k$ the partial sums of the two coordinates).
--
--   Role: turns the block constructions of the two KMT cases into the infinite coupling the parent needs.
--
--   **Formalization Note**: the infinite coupling is built from independent couplings of the consecutive blocks of lengths $2^{2^j}$.
-- source:
--   Komlós, Major, Tusnády, An approximation of partial sums of independent RV'-s and the sample DF. I, Z. Wahrsch. verw. Gebiete 32 (1975) 111-131, https://static.renyi.hu/~major/articles/KMT1.pdf, Section 3 (Proof of Theorem 1), pp. 116-118, construction along the dyadic blocks; and Komlós, Major, Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 4, end of the proof of Theorem 1B, p. 51

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz

theorem kmt_dyadic_blocks_glue (F : Measure ℝ) [IsProbabilityMeasure F]
    (h : ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
        ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
          Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => F) ∧
          Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
          ∀ x : ℝ, 0 < x →
            Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
              |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
                (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
              ENNReal.ofReal (K * Real.exp (-lam * x))) :
    ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F) ∧
      Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
            |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by sorry

end EthierKurtz
