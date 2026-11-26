-- Prove2me | Theorems.Thm_Erdos287_top_layer_multiplicity_residues
-- name    : Erdos287.top_layer_multiplicity_residues
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:43:20.328494+00:00
-- url     : https://prove2.me/theorems/5f4391f9-55c3-5b77-88ef-25b709785834
-- title:
--   Top-layer translation bound from cofactor residue multiplicities
-- statement:
--   Let $T$ be a fixed set of offsets for the cofactors of the selected multiples of $p^e$ in a unit-fraction representation, with no selected multiple of $p^{e+1}$. Write $U$ for the offset residue classes whose multiplicities in $T$ are nonzero modulo $p$. If $U$ is nonempty, at most $|U|-1$ translation residues $c\bmod p$ can occur for the cofactors $c+T$. The bound is independent of the size of $T$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.top_layer_multiplicity_residues (p : ℕ) (hp : p.Prime) (T : Finset ℕ) :
    ∃ (U R : Finset (ZMod p)),
      (∀ u : ZMod p, u ∈ U ↔ ((T.filter (fun d : ℕ => (d : ZMod p) = u)).card : ZMod p) ≠ 0) ∧
      R.card ≤ U.card - 1 ∧
      ∀ (D : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
        (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        (∀ n ∈ D, ¬ p ^ (e + 1) ∣ n) →
        T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
        U.Nonempty → (c : ZMod p) ∈ R := by sorry
