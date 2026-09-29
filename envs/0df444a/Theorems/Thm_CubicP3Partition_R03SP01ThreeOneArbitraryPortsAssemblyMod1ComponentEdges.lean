-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsAssemblyMod1ComponentEdges
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsAssemblyMod1ComponentEdges
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:20:19.403982+00:00
-- url     : https://prove2.me/theorems/83001f52-e324-4bdd-b8d6-7382e2e1e4ca
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneArbitraryPortsAssemblyMod1ComponentEdges
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsAssemblyMod1ComponentEdges` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 3e243d801ed1d5003707a8e2075cfa9290f536f253cf26cac89be1d4e6edcba7.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-assembly-mod1-component-edges-candidate-v1.lean; source SHA-256 3e243d801ed1d5003707a8e2075cfa9290f536f253cf26cac89be1d4e6edcba7; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01ThreeOneArbitraryPortsAssemblyMod1ComponentEdges
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3))
    (hAraw : ∀ i : Fin a,
      G.Adj
          (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (0 : Fin 3)))))))
          (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (1 : Fin 3))))))) ∧
      G.Adj
          (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (1 : Fin 3)))))))
          (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (2 : Fin 3))))))))
    (hB1raw : ∀ i : Fin k1,
      G.Adj
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inl (finProdFinEquiv
            (i, (0 : Fin 3))))))))
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inl (finProdFinEquiv
            (i, (1 : Fin 3)))))))) ∧
      G.Adj
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inl (finProdFinEquiv
            (i, (1 : Fin 3))))))))
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inl (finProdFinEquiv
            (i, (2 : Fin 3)))))))))
    (hB2raw : ∀ i : Fin k2,
      G.Adj
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv
            (i, (0 : Fin 3)))))))))
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv
            (i, (1 : Fin 3))))))))) ∧
      G.Adj
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv
            (i, (1 : Fin 3)))))))))
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv
            (i, (2 : Fin 3))))))))))
    (hCraw : ∀ i : Fin c,
      G.Adj
          (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans
            (finAddFlip (m := c * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (0 : Fin 3))))))))
          (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans
            (finAddFlip (m := c * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (1 : Fin 3)))))))) ∧
      G.Adj
          (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans
            (finAddFlip (m := c * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (1 : Fin 3))))))))
          (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans
            (finAddFlip (m := c * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (2 : Fin 3)))))))))
    (hAB : G.Adj (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (3 : Fin 4))))))) (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (0 : Fin 4))))))))
    (hB01 : G.Adj (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (0 : Fin 4))))))) (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1))) (Sum.inr (0 : Fin 1))))))
    (hB23 : G.Adj (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans (finAddFlip (m := c * 3) (n := 1))) (Sum.inr (0 : Fin 1)))))) (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (1 : Fin 4))))))))
    (hBC : G.Adj (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (1 : Fin 4))))))) (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (2 : Fin 4)))))))) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
