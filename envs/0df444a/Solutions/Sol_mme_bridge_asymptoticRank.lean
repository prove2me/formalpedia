-- Prove2me | solution 1 for mme_bridge_asymptoticRank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-30T19:10:32.918827+00:00
-- url     : https://prove2.me/submissions/c15b4831-3b4f-4cf7-b962-4d05a0ce9a0f

import Definitions.Def_mme_tensor_bridge

/-! # Solution: bridge A — abstract `asymptoticRank` ↔ concrete `tensorAsymptoticRank`

The proof is the 5-line rewrite chain `bridge_asymptoticRank` already established in
`Def_mme_tensor_bridge`: identify `tensorPreorder K` with `TensorQ.tensorStrassen K 3`
(both have the same `le`), rewrite via `tensorAsymptoticRank_eq` and `toQ_bigAdd`,
finish by `rfl`. Re-exported here as a first-class Theorem-node leaf so downstream
reductions can cite it directly. -/

open MME BigOperators

universe u

theorem solution {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) :
    StrassenPreorder.asymptoticRank (tensorPreorder K)
        (∑ i, MMq K (n i) (m i) (p i)) =
      tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) :=
  MME.bridge_asymptoticRank n m p
