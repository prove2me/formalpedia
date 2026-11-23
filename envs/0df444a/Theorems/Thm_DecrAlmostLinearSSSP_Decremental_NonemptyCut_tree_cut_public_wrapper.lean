-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_tree_cut_public_wrapper
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.tree_cut_public_wrapper
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:15.810729+00:00
-- url     : https://prove2.me/theorems/d61e2ede-56b9-47d7-ae5d-dd1880077490
-- title:
--   Charged scaling and complete report-draining wrapper for tree cuts
-- statement:
--   Suppose a normalized tree implementation has quality $K_0$, operation factor $h_0$, initialization envelope $a_0$ and constant $C_0>0$, with the displayed exponential quality bound. Then there is a full public dynamic-cut implementation with quality $K\ge32$, subpolynomial operation, report and initialization factors, and the same form of quality bound.
--
--   The construction normalizes capacities by $S=M^d$, where $M=\max\{2,m\}$. If the tree returns $\widehat U$, the public value is $U=\widehat U/S$. Potentials and baselines are represented as $\widehat y=y/S$ and $\widehat b=b/S$, and a public toggle $\tau$ is forwarded as $\widehat\tau=\tau/S$. Consequently,
--   $$
--   \widehat\tau\le1/\widehat U,\qquad
--   \widehat u_e\bigl(D\widehat y_e-\widehat b_e\bigr)=u_e\bigl(Dy_e-b_e\bigr),
--   $$
--   so tree-toggle legality and detector thresholds match the public semantics exactly. Potential-query results are multiplied by $S$.
--
--   After each toggle the wrapper repeatedly executes `peek`; each positive answer is emitted once and followed by `reset`, and draining stops only after the exact negative certificate. Thus the completed public operation reports precisely the active threshold set and resets exactly its baselines. Non-toggle operations emit no reports. The capacity-weighted variation telescope gives $R\le T/\xi$, so one may take $\Gamma=1$. A toggle with $r$ reports causes $1+r$ peeks and $r$ resets; hence the number of charged tree calls over a public trace is at most $2q+2R$, yielding an $m^{o(1)}(q+R)$ public work envelope after padding. Initialization, scaling arithmetic, output writes and all private calls are included in actual RAM work.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p.9, Lemma 3.2 and §3.2.1 ToggleCut/report bound, p.10 Repair step 1 (process all pending reports), and p.16 numerical range; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. Generic charged construction of the public interface from DecrAlmostLinearSSSP_TreeCutProtocol.

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false
open scoped ENNReal NNReal

/-- A charged wrapper turns the normalized lazy tree structure into the full public
cut implementation, including scaling, complete report draining and report accounting. -/
theorem DecrAlmostLinearSSSP.Decremental.NonemptyCut.tree_cut_public_wrapper (exponent : ℕ) (tree : TreeImplementation)
    (K₀ h₀ a₀ : ℕ → ℝ) (C₀ : ℝ) :
    0 < C₀ → Subpolynomial K₀ → Subpolynomial h₀ → Subpolynomial a₀ →
    (∀ m, K₀ m ≤ Real.rpow 2
      (C₀ * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
        max 1 (Real.log (Real.log (max 2 m : ℕ))))) →
    (∀ m ξ, 0 < ξ → TreeImplements tree m exponent (K₀ m) (h₀ m)
      (C₀ * m * a₀ m) ξ) →
    ∃ (impl : Implementation) (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      ∀ m ξ, 0 < ξ → Implements impl m exponent (K m) (h m) (Γ m)
        (C * m * a m) ξ := by sorry
