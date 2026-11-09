-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_theorem_3_6
-- name    : ExactLearningSeparation678.Randomized.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:13.401835+00:00
-- url     : https://prove2.me/theorems/bdc67a3a-ee50-4a35-9bc4-04689da0ee7d
-- title:
--   Theorem 3.6 — quantum query upper bound
-- statement:
--   There is an absolute $K>0$ such that for every $t=2^m$ with $m\ge2$, the actual quantum exact-learning complexity satisfies
--   $$Q(C_t)\le(K+1)t.$$
--   More precisely, some input-independent learner uses $T_0+t$ membership queries, where $T_0\le Kt$, and identifies every target with probability at least $1-1/t$. The exceptional Fourier mass of Eq. (11) is at most $1/t$ for every polynomial. For every slope $s$ and coefficient index $j$, a single-query algorithm fixed before the coefficients recovers $a_j$ with probability one from the full membership oracle. There are $t$ such coefficient indices.
--
--   This is a bound on identifying the entire concept, including its polynomial. The constant is uniform over the growing parameter and all targets; it is not a supplied bound on a chosen learner.
--
--   **Formalization Note** The source gives the amplification cost only as $O(t)$. Its uniform existential prefactor is left unspecified. The success lower bound is at least $3/4$ throughout the stated domain.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
--   - encoding: Q(C_t) = O(t), with failure at most 1/t and t exact coefficient queries in the proof → one positive absolute K precedes every m; Q_t ≤ (K+1)t and a (T₀+t)-query learner has T₀ ≤ Kt and success ≥ 1−1/t, together with the Fourier mass bound and exact one-query recovery of each coefficient; reason: retains the proof’s explicit quantitative guarantees without inventing a numerical amplitude-amplification prefactor
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 3.6, pp.19–21; Eqs. (9)–(11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Construction

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Theorem 3.6, pp.19–21, including Eq.(11) failure ≤1/t and exact one-query coefficient recovery. K is absolute; the source supplies no numerical amplification prefactor. -/
theorem theorem_3_6 : ∃ K : ℝ, 0 < K ∧ ∀ m : Size,
    (Q m : ℝ) ≤ (K + 1) * t m ∧
    (∃ (T₀ w : ℕ) (A : QAlgorithms.QueryAlg (Domain m) Bool (Fin w) (T₀ + t m))
      (out : (Domain m × Bool) × Fin w → (Domain m → Bool)),
      (T₀ : ℝ) ≤ K * t m ∧
      ∀ p : Parameters m,
        A.outputProb (QAlgorithms.xorOracle (concept m p)) out (concept m p) ≥
          1 - 1 / (t m : ℝ)) ∧
    (∀ a : Coeff m, fourierFailure m a ≤ 1 / (t m : ℝ)) ∧
    (∀ (s : F m) (j : Fin (t m)),
      ∃ (w : ℕ) (A : QAlgorithms.QueryAlg (Domain m) Bool (Fin w) 1)
        (out : (Domain m × Bool) × Fin w → F m),
        ∀ a : Coeff m,
          A.outputProb (QAlgorithms.xorOracle (concept m (a, s))) out (a j) = 1) := by sorry

end ExactLearningSeparation678.Randomized
