-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01V2CyclicResidualAssembly
-- name    : CubicP3Partition.R03SP01V2CyclicResidualAssembly
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:09:35.432252+00:00
-- url     : https://prove2.me/theorems/9afcab8a-51d1-45ee-a63f-2d4728e6a674
-- title:
--   R03 P3-factor structural result: R03SP01V2CyclicResidualAssembly
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01V2CyclicResidualAssembly` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 0121c1ff02b51e43b750af9dc22551a4d35d467f969b0a7fc7972c67c738aba5.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-cyclic-residual-assembly-candidate-v1.lean; source SHA-256 0121c1ff02b51e43b750af9dc22551a4d35d467f969b0a7fc7972c67c738aba5; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_de73be8e06_r03_sp01_cyclic_residual_assembly_candidate_v1

namespace CubicP3Partition

open CubicP3Partition
universe u v
theorem R03SP01V2CyclicResidualAssembly
    {ι : Type u} [Fintype ι]
    {V : ι → Type u} [∀ i, Fintype (V i)]
    {W : Type u} [Fintype W]
    (Gi : ∀ i, SimpleGraph (V i))
    (G : SimpleGraph W)
    (n k r : ι → Nat)
    (eV : ∀ i, Fin (n i) ≃ V i)
    (hsize : ∀ i, n i = k i * 3 + r i)
    (successorEdge : ∀ (i : ι) (j : Fin (n i))
      (h : j.val + 1 < n i),
      (Gi i).Adj (eV i j) (eV i ⟨j.val + 1, h⟩))
    {R : Type u} [Fintype R]
    (GR : SimpleGraph R)
    (pR : P3Factor GR)
    (eTotal :
      (Σ o : Option ι,
        match o with
        | none => R
        | some i => {x : V i // x ∈ R03SP01V2SuffixSet (n i) (k i) (r i) (eV i)}) ≃ W)
    (hResidual : ∀ {x y : R}, GR.Adj x y →
      G.Adj (eTotal ⟨none, x⟩) (eTotal ⟨none, y⟩))
    (hSuffix : ∀ (i : ι) {x y : {x : V i //
        x ∈ R03SP01V2SuffixSet (n i) (k i) (r i) (eV i)}},
      ((Gi i).induce (R03SP01V2SuffixSet (n i) (k i) (r i) (eV i))).Adj x y →
      G.Adj (eTotal ⟨some i, x⟩) (eTotal ⟨some i, y⟩)) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
