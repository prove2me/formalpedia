-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_outer_facts
-- name    : CSSNearGV.Amplification.outer_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:24.804215+00:00
-- url     : https://prove2.me/theorems/f87bf40a-f482-4b11-8502-5bd0e0f5850b
-- title:
--   Proposition 3.5 — outer parity enumerator and entropy bounds
-- statement:
--   Let $s\ge2$ be even, $n=sb>0$, and let $\Phi(a)$ count weight-$a$ block-parity words. Put $a'=\min(a,n-a)$. The eight assertions of Proposition 3.5 hold:
--   $$\Phi(n-a)=\Phi(a),\quad \Phi(1)=\Phi(n-1)=0,\quad \Phi(a)\le(s-1)^{a'/2}\binom{n/2}{a/2},$$
--   $$\Phi(a)\alpha^a(1-\alpha)^{n-a}\le\left(\frac{1+(1-2\alpha)^s}{2}\right)^{n/s},\qquad
--   \Phi(a)\le\operatorname{poly}(n)\binom na^{1-1/s}.$$
--   The last bound is uniform in $a$. Both $\varphi$ and $\varphi-h$ are symmetric about $1/2$; on $[0,1/2]$ the former is nondecreasing and the latter nonincreasing. Finally $\varphi(\gamma)\ge h(\gamma)-1/s$ on $[0,1]$. The binomial lower index for an odd $a$ can be floored since its left side is zero.
--
--   These estimates describe the outer code for the finite and spectral analyses.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: poly(n), soft-O and negligible estimates → eventual inequalities with positive constants, exponents and thresholds fixed before length and all weights; reason: the source leaves numerical prefactors unspecified; parameters s, m and epsilon are fixed before these constants
--   - reading: increasing and decreasing → nondecreasing and nonincreasing; reason: the spectral shapes have zero plateaus, as used explicitly in the paper
--   - encoding: binomial lower index a/2 for the even-weight parity enumerator → natural division a/2 in Nat.choose, also at odd a; reason: even indices are exact; every odd-weight enumerator coefficient is zero, so rounding its unused binomial index changes no bound
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Proposition 3.5, printed pp.11–12 / PDF 13–14; proof printed pp.27–28 / PDF 29–30

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem outer_facts (s : ℕ) (hs : 2 ≤ s) (he : Even s) :
  (∀ b a : ℕ, 1 ≤ b → a ≤ s * b → phiFinite s b (s * b - a) = phiFinite s b a) ∧
  (∀ b : ℕ, 1 ≤ b → phiFinite s b 1 = 0 ∧ phiFinite s b (s * b - 1) = 0) ∧
  (∀ b a : ℕ, 1 ≤ b → a ≤ s * b →
    (phiFinite s b a : ℝ) ≤ (s - 1 : ℝ) ^ ((min a (s * b - a) : ℝ) / 2) *
      ((s * b / 2).choose (a / 2) : ℝ)) ∧
  (∀ b a : ℕ, 1 ≤ b → a ≤ s * b → ∀ α ∈ Set.Icc (0 : ℝ) 1,
    (phiFinite s b a : ℝ) * α ^ a * (1 - α) ^ (s * b - a) ≤
      ((1 + (1 - 2 * α) ^ s) / 2) ^ b) ∧
  (∃ C : ℝ, 0 < C ∧ ∃ q N : ℕ, ∀ b a : ℕ, 1 ≤ b → N ≤ s * b → a ≤ s * b →
    (phiFinite s b a : ℝ) ≤ C * (s * b : ℝ) ^ q *
      ((s * b).choose a : ℝ) ^ (1 - 1 / (s : ℝ))) ∧
  Symmetric (phi s) ∧ MonotoneOn (phi s) (Set.Icc 0 (1 / 2)) ∧
  Symmetric (fun γ => phi s γ - entropy γ) ∧
  AntitoneOn (fun γ => phi s γ - entropy γ) (Set.Icc 0 (1 / 2)) ∧
  (∀ γ ∈ Set.Icc (0 : ℝ) 1, entropy γ - 1 / (s : ℝ) ≤ phi s γ) := by sorry

end CSSNearGV.Amplification
