-- Prove2me | Theorems.Thm_ComputationalLearning_vc_lower_bound
-- name    : ComputationalLearning.vc_lower_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:13:44.116994+00:00
-- url     : https://prove2.me/theorems/439c2f88-6e52-4677-a94b-5719ff1d4b3f
-- title:
--   Theorem 3.5: PAC learning a class of VC dimension d needs Ω(d/ε) examples; explicit forms m ≤ d/2 and m ≤ (d−1)/(64ε)
-- statement:
--   **Theorem 3.5.** Any algorithm for PAC learning a concept class of Vapnik–Chervonenkis dimension $d$ must use $\Omega(d/\epsilon)$ examples in the worst case.
--
--   Formally, for a class $C$ shattering a set of $d \ge 1$ points on an instance space with measurable singletons, and every learning function $L$ on samples of size $m$: (i) if $m \le d/2$, there are a target $c \in C$ and a distribution $D$ (uniform on the shattered set) such that the error of $L$'s hypothesis is at least $1/8$ with probability at least $1/2$ over the sample (the book's first argument: the labels of unseen points are fair coins); (ii) if $0 < \epsilon \le 1/16$ and $m \le (d-1)/(64\epsilon)$, there are $c \in C$ and $D$ (one point of weight $1 - 16\epsilon$, the others of weight $16\epsilon/(d-1)$) such that the error exceeds $\epsilon$ with probability at least $1/4$. The constants in (ii) instantiate the book's $\Omega(d/\epsilon)$: with fewer than $(d-1)/(64\epsilon)$ examples the algorithm fails with probability at least $1/4$ for some target and distribution.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §3.6 pp. 62-64, Theorem 3.5 with its proof (the coin-flipping construction and its scaling to weight 8ε)

import Definitions.Def_ComputationalLearning_VC

open MeasureTheory

namespace ComputationalLearning

/-- **Theorem 3.5** (p. 62). Any algorithm for PAC learning a concept class of VC dimension `d`
must use `Ω(d/ε)` examples in the worst case. Stated with the two explicit forms of the proof
(pp. 62–64), for a class shattering some set of `d ≥ 1` points, on an instance space with
measurable singletons, and for every learning function `L` on samples of size `m`:
(i) if `m ≤ d/2`, some target concept in the class and some distribution make the error of
`L`'s hypothesis at least `1/8` with probability at least `1/2`;
(ii) if `ε ≤ 1/16` and `m ≤ (d − 1)/(64ε)`, some target concept and some distribution make the
error greater than `ε` with probability at least `1/4` (so a PAC algorithm with `δ < 1/4` needs
more than `(d − 1)/(64ε)` examples). -/
theorem vc_lower_bound {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Set (X → Bool)) (d : ℕ) (hd1 : 1 ≤ d) (hd : (d : ℕ∞) ≤ vcDim C) (m : ℕ)
    (L : (Fin m → X × Bool) → X → Bool) :
    ((m : ℝ) ≤ d / 2 → ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
      ENNReal.ofReal (1 / 2) ≤ sampleLaw D c m {S | 1 / 8 ≤ errorOf D c (L S)}) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → (m : ℝ) ≤ (d - 1) / (64 * ε) →
      ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
        ENNReal.ofReal (1 / 4) ≤ sampleLaw D c m {S | ε < errorOf D c (L S)}) := by sorry

end ComputationalLearning
