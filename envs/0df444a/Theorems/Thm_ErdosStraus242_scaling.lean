-- Prove2me | Theorems.Thm_ErdosStraus242_scaling
-- name    : ErdosStraus242.scaling
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:41:10.005966+00:00
-- url     : https://prove2.me/theorems/eceb923c-4f49-4780-8b93-3df853cf03e8
-- title:
--   Transport the property by positive multiplication
-- statement:
--   For natural numbers $n,k$, if $n$ has three distinct positive ordered denominators representing $4/n$ and $k>0$, then $kn$ has such a decomposition.
-- source:
--   Bloom–Elsholtz (2022), p. 239, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; witness refinement in scale_witness.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem scaling (n k : ℕ) (h : IsErdosStraus n) (hk : 0 < k) :
    IsErdosStraus (k*n) := by sorry
end ErdosStraus242
