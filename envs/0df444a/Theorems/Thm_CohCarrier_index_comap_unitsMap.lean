-- Prove2me | Theorems.Thm_CohCarrier_index_comap_unitsMap
-- name    : CohCarrier.index_comap_unitsMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/192a9ed1-b022-5fe7-a803-5da3a0fbd491
-- title:
--   Index is preserved under pullback along (ℤ/M')^×→(ℤ/M)^×
-- statement:
--   Let $M$ and $M'$ be natural numbers with $M'$ nonzero, and suppose $M \mid M'$. Let $H_0$ be a subgroup of the unit group $(\mathbb Z/M\mathbb Z)^\times$. The reduction homomorphism on units associated with the divisibility $M \mid M'$, namely `ZMod.unitsMap hMM'` $\colon (\mathbb Z/M'\mathbb Z)^\times \to (\mathbb Z/M\mathbb Z)^\times$, pulls $H_0$ back to the subgroup $H_0.\mathrm{comap}$ of $(\mathbb Z/M'\mathbb Z)^\times$ consisting of all units of $\mathbb Z/M'\mathbb Z$ whose reduction modulo $M$ lies in $H_0$. The assertion is the equality of indices
--   $$[(\mathbb Z/M'\mathbb Z)^\times : H_0.\mathrm{comap}] = [(\mathbb Z/M\mathbb Z)^\times : H_0],$$
--   an equality of natural numbers in Mathlib's convention, where an index is $0$ when the number of cosets is infinite (here both sides are finite, as $M'$ is nonzero). No finiteness, triviality or saturation hypothesis on $H_0$ is imposed beyond $M \mid M'$ and $M' \neq 0$.
--
--   This is the standard compatibility of unit-group indices with change of level: the full preimage of $H_0 \le (\mathbb Z/M\mathbb Z)^\times$ in $(\mathbb Z/M'\mathbb Z)^\times$ has the same index, so a level structure $\Gamma_H$ may be raised from level $M$ to level $M'$ without altering $[(\mathbb Z/M\mathbb Z)^\times : H]$. It is used where an invertibility or divisibility condition on this index must be carried along a degeneracy map that multiplies the level, in the construction of refinement and corner data for local Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_index_comap_unitsMap.lean

import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.index_comap_unitsMap
    {M M' : ℕ} [NeZero M'] (hMM' : M ∣ M') (H₀ : Subgroup (ZMod M)ˣ) :
    (H₀.comap (ZMod.unitsMap hMM')).index = H₀.index := by sorry
