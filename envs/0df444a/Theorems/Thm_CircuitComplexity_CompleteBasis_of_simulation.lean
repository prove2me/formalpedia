-- Prove2me | Theorems.Thm_CircuitComplexity_CompleteBasis_of_simulation
-- name    : CircuitComplexity.CompleteBasis.of_simulation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:04.504918+00:00
-- url     : https://prove2.me/theorems/8c97840f-2307-4815-9dfc-6fcfd08f3579
-- title:
--   Complete Basis: of simulation
-- statement:
--   If every circuit over `B₁` can be simulated by a circuit over `B₂`
--       (possibly with a different number of internal gates), then completeness
--       of `B₁` implies completeness of `B₂`.
--
--       This is the generic tool for proving new bases complete: show you can
--       compile each gate of a known-complete basis into a subcircuit of the
--       new basis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L210-L217
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L210-L217

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.CompleteBasis.of_simulation (B₁ B₂ : Basis) [CompleteBasis B₁]
    (sim : ∀ {N M G} [NeZero N] [NeZero M] (c : Circuit B₁ N M G),
      ∃ G', ∃ c' : Circuit B₂ N M G', c'.eval = c.eval)
    : CompleteBasis B₂ := by sorry
