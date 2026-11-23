-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_subpolynomial_wrapper_parameters
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.subpolynomial_wrapper_parameters
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:01.088857+00:00
-- url     : https://prove2.me/theorems/b77cf8d9-152c-4a99-8071-72d58217a526
-- title:
--   Subpolynomial padding and scaled maxima for tree-cut wrapper parameters
-- statement:
--   Let $K_0,h_0,a_0$ be subpolynomial in the mission's sense, namely strictly positive and satisfying $\log f(m)/\log\max(2,m)\to0$. Suppose $C_0>0$ and, writing $L(m)=\log\max(2,m)$,
--   $$K_0(m)\le 2^{C_0L(m)^{5/6}\max(1,\log L(m))}$$
--   for every $m$. Then there is $C>0$ such that $K(m)=\max(32,K_0(m))$ is subpolynomial, is everywhere at least $32$, and satisfies the same envelope with $C$ replacing $C_0$. Moreover, for all positive constants $c,d$, the functions $c\max(1,h_0)$, $c\max(1,a_0)$ and $\max(c\max(1,h_0),d\max(1,a_0))$ are subpolynomial, and the constant function $\Gamma=1$ is subpolynomial. One admissible choice is
--   $$C=C_0+\frac{5}{(\log2)^{5/6}}.$$
--   This is general parameter algebra supporting the charged scaling and report-draining tree-cut wrapper; it does not assert existence of the dynamic data structure itself.
-- source:
--   STOC 2027 submission #912, Lemma 3.2, p. 9: the dynamic minimum-ratio cut interface uses $m^{o(1)}$ terms and clipped logarithmic multipliers. This theorem formalizes only the pointwise positivity/limit algebra and envelope padding needed by the public tree-cut wrapper (`tree_cut_public_wrapper`), with $K=\max(32,K_0)$ and $\Gamma=1$; it is not a separate claim that an implementation exists.

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false

open scoped ENNReal NNReal

/-- Supporting parameter algebra for the public tree-cut wrapper. -/
theorem DecrAlmostLinearSSSP.Decremental.NonemptyCut.subpolynomial_wrapper_parameters {K₀ h₀ a₀ : ℕ → ℝ} {C₀ : ℝ}
    (hC₀ : 0 < C₀) (hK₀ : DecrAlmostLinearSSSP.Decremental.Subpolynomial K₀) (hh₀ : DecrAlmostLinearSSSP.Decremental.Subpolynomial h₀)
    (ha₀ : DecrAlmostLinearSSSP.Decremental.Subpolynomial a₀)
    (hbound : ∀ m, K₀ m ≤ Real.rpow 2
      (C₀ * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
        max 1 (Real.log (Real.log (max 2 m : ℕ))))) :
    ∃ C : ℝ, 0 < C ∧
      DecrAlmostLinearSSSP.Decremental.Subpolynomial (fun m => max 32 (K₀ m)) ∧
      (∀ c : ℝ, 0 < c → DecrAlmostLinearSSSP.Decremental.Subpolynomial (fun m => c * max 1 (h₀ m))) ∧
      (∀ c : ℝ, 0 < c → DecrAlmostLinearSSSP.Decremental.Subpolynomial (fun m => c * max 1 (a₀ m))) ∧
      (∀ c d : ℝ, 0 < c → 0 < d →
        DecrAlmostLinearSSSP.Decremental.Subpolynomial (fun m => max (c * max 1 (h₀ m)) (d * max 1 (a₀ m)))) ∧
      DecrAlmostLinearSSSP.Decremental.Subpolynomial (fun _ : ℕ => (1 : ℝ)) ∧
      (∀ m, 32 ≤ max 32 (K₀ m)) ∧
      ∀ m, max 32 (K₀ m) ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ)))) := by sorry
