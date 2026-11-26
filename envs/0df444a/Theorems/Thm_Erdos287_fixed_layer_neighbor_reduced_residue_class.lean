-- Prove2me | Theorems.Thm_Erdos287_fixed_layer_neighbor_reduced_residue_class
-- name    : Erdos287.fixed_layer_neighbor_reduced_residue_class
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:17:05.873384+00:00
-- url     : https://prove2.me/theorems/7f04a7b5-ceae-449b-addf-755d288ce364
-- title:
--   A fixed signed adjacency lies in one reduced residue class
-- statement:
--   Fix natural numbers $p,b$ and a sign $\epsilon\in\{-1,1\}$. If $a_0p=bq_0+\epsilon$, then $p$ is coprime to both $b$ and $q_0$. Any other solution $ap=bq+\epsilon$ satisfies $q\equiv q_0\pmod p$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.fixed_layer_neighbor_reduced_residue_class (p b a₀ q₀ : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1)
    (h₀ : (a₀ : ℤ) * p = (b : ℤ) * q₀ + e) :
    p.Coprime b ∧ p.Coprime q₀ ∧
      ∀ a q : ℕ, (a : ℤ) * p = (b : ℤ) * q + e → q ≡ q₀ [MOD p] := by sorry
