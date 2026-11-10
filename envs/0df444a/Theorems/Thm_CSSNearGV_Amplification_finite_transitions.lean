-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_finite_transitions
-- name    : CSSNearGV.Amplification.finite_transitions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:43.596493+00:00
-- url     : https://prove2.me/theorems/860d6ca2-3381-443f-b9b9-a714e84d1bb7
-- title:
--   Proposition 5.6 — exact finite transition bounds
-- statement:
--   For positive admissible blocklength $n$ and positive weights $a,b,c\le n$, set $a'=\min(a,n-a)$ and similarly for $b',c'$. Then
--   $$p_A(a,b)\le\left(\frac{4(b'+1)}n\right)^{\lceil a/2\rceil},\qquad
--   p_D(a,b)\le\frac{(a'n)^{\lfloor b/2\rfloor}}{(\lfloor b/2\rfloor!)^2\binom na},$$
--   $$p_D(a,b)p_A(b,c)\le\frac{(4a'(c'+1))^{\lfloor b/2\rfloor}}{(\lfloor b/2\rfloor!)^2\binom na}
--   \le\frac{(4a'(c'+1))^{\lfloor b/2\rfloor}}{\binom na},$$
--   $$p_A(a,b),p_D(a,b)\le\min\{1,\binom nb/\binom na\}.$$
--   For any fixed $k\ge1$, sequence of A/D operations, and positive weight sequence,
--   $$\Phi(a_0)\prod_{i=1}^k p_{T_i}(a_{i-1},a_i)\le\frac{\operatorname{poly}(n)\binom n{a_k}}{\binom n{a_{k-1}}^{1/s}}.$$
--   The polynomial bound is uniform in every weight and choice of operations. These finite bounds retain the source floors and ceilings for the boundary analysis.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: poly(n), soft-O and negligible estimates → eventual inequalities with positive constants, exponents and thresholds fixed before length and all weights; reason: the source leaves numerical prefactors unspecified; parameters s, m and epsilon are fixed before these constants
--   - encoding: positive-weight finite-ratio bounds in Section 5.2, with zero omitted from the recursion → every weight lies in Finset.Icc 1 n; reason: this makes the section convention explicit and keeps every binomial denominator positive; zero transitions remain defined operationally in Ensemble
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Proposition 5.6, printed p.19 / PDF 21; proof pp.31–32 / PDF 33–34

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem finite_transitions (s : ℕ) (hs : 2 ≤ s) (he : Even s) :
  (∀ b a t c : ℕ, 1 ≤ b → a ∈ Finset.Icc 1 (s * b) → t ∈ Finset.Icc 1 (s * b) →
    c ∈ Finset.Icc 1 (s * b) →
    let n := s * b
    let a' := min a (n - a)
    let c' := min c (n - c)
    transition n true a t ≤ (4 * ((min t (n - t) : ℝ) + 1) / n) ^ ((a + 1) / 2) ∧
    transition n false a t ≤ ((a' * n : ℕ) : ℝ) ^ (t / 2) /
      (((t / 2).factorial : ℝ) ^ 2 * (n.choose a : ℝ)) ∧
    transition n false a t * transition n true t c ≤
      (4 * (a' : ℝ) * (c' + 1)) ^ (t / 2) / (((t / 2).factorial : ℝ) ^ 2 * (n.choose a : ℝ)) ∧
    (4 * (a' : ℝ) * (c' + 1)) ^ (t / 2) / (((t / 2).factorial : ℝ) ^ 2 * (n.choose a : ℝ)) ≤
      (4 * (a' : ℝ) * (c' + 1)) ^ (t / 2) / (n.choose a : ℝ) ∧
    transition n true a t ≤ min 1 ((n.choose t : ℝ) / (n.choose a : ℝ)) ∧
    transition n false a t ≤ min 1 ((n.choose t : ℝ) / (n.choose a : ℝ))) ∧
  (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∃ q N : ℕ, ∀ b : ℕ, 1 ≤ b → N ≤ s * b →
    ∀ (types : Fin k → Bool) (a : Fin (k + 1) → ℕ),
      (∀ i, a i ∈ Finset.Icc 1 (s * b)) →
      (phiFinite s b (a 0) : ℝ) *
        (∏ i : Fin k, transition (s * b) (types i) (a i.castSucc) (a i.succ)) ≤
        C * (s * b : ℝ) ^ q * ((s * b).choose (a ⟨k, by omega⟩) : ℝ) /
          ((s * b).choose (a ⟨k - 1, by omega⟩) : ℝ) ^ (1 / (s : ℝ))) := by sorry

end CSSNearGV.Amplification
