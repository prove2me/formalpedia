-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01FivePieceSourceAssembly
-- name    : CubicP3Partition.R03SP01FivePieceSourceAssembly
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:44:35.979357+00:00
-- url     : https://prove2.me/theorems/f57c905f-c4e4-43ae-b130-7f590aea5853
-- title:
--   R03 P3-factor structural result: R03 s p01 five piece source assembly
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01FivePieceSourceAssembly` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-five-piece-source-assembly-candidate-v1.lean; source SHA-256 9385a09ca243c75a2213e63db449bab3e90d4618124c1163a8622e84b7e4d7d8; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01FivePieceSourceAssembly
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (a k1 k2 c : Nat)
    (target :
      (((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) ≃
        (A ⊕ (B ⊕ C))))
    (hA : ∀ i : Fin a,
      G.Adj (target (Sum.inl (i, (0 : Fin 3))))
        (target (Sum.inl (i, (1 : Fin 3)))) ∧
      G.Adj (target (Sum.inl (i, (1 : Fin 3))))
        (target (Sum.inl (i, (2 : Fin 3)))))
    (hB1 : ∀ i : Fin k1,
      G.Adj (target (Sum.inr (Sum.inl (i, (0 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (1 : Fin 3))))) ∧
      G.Adj (target (Sum.inr (Sum.inl (i, (1 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (2 : Fin 3))))))
    (hB2 : ∀ i : Fin k2,
      G.Adj (target (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3))))))
        (target (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))) ∧
      G.Adj (target (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))
        (target (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3)))))))
    (hC : ∀ i : Fin c,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))) ∧
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3))))))))
    (hExc01 : ∀ i : Fin 2,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))))
    (hExc12 : ∀ i : Fin 2,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3)))))))) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
