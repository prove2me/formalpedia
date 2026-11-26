-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_normalize_weighted_path_parity
-- name    : DirectedHamiltonicity.Main.normalize_weighted_path_parity
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:24:30.347412+00:00
-- url     : https://prove2.me/theorems/32e2a013-9bbc-567c-99a2-c5cc0bc222e9
-- title:
--   Proposition 4: normalization preserves every weighted Hamiltonian-path parity
-- statement:
--   Every finite directed multigraph with nonnegative arc weights can be replaced, on the same vertices, by a normalized weighted multigraph having no more arcs and no new incoming weights. Every retained arc label (tail, head, weight) occurs in the input. The two weighted Hamiltonian-path counts agree modulo two for every integer target, simultaneously. This includes parallel arcs of the same weight, loops, arcs into the source, and arcs out of the target.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission #811. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf Normalization preceding the determinant-sum argument in Proposition 4, PDF pp. 7–8.

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph

open Classical in
theorem DirectedHamiltonicity.Main.normalize_weighted_path_parity {V E : Type} [Fintype V] [Fintype E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) :
    ∃ (F : Type) (ff : Fintype F) (G : Multidigraph V F) (z : F → ℕ),
      letI := ff
      G.IsNormalized z s t ∧ Fintype.card F ≤ Fintype.card E ∧
      (∀ v, G.incomingWeights z v ⊆ H.incomingWeights w v) ∧
      (∀ f, ∃ e, H.tail e=G.tail f ∧ H.head e=G.head f ∧ w e=z f) ∧
      ∀ B : ℤ, (H.weightedPathCount w s t B : ZMod 2) = (G.weightedPathCount z s t B : ZMod 2) := by sorry
