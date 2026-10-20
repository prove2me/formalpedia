-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exists_chain_energy_of_step
-- name    : DerivativeChainPrivate.exists_chain_energy_of_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:42:18.743784+00:00
-- url     : https://prove2.me/theorems/691f4f2f-9fcb-41b0-aa66-a26b7d22da48
-- title:
--   Compatible chain energy from a stated one-step hypothesis
-- statement:
--   Assume explicitly that every critical point w of every positive-degree complex polynomial P has an actual root v with |v-w|^2<=|v|^2-|w|^2. For any n>0, any n complex root slots a, and any root u of their degree-one derivative row, there exists a complete derivative-root chain z starting at u such that
--
--   $$\sum_{i=0}^{n-2}|z_{i+1}-z_i|^2\le|z_{n-1}|^2-|u|^2.$$
--
--   This is a conditional chain-construction lemma. It does not assert the one-step hypothesis; the later unconditional polynomial theorem supplies that hypothesis by a separate proved lemma. No disk assumption is used here.
-- source:
--   Derivative-zero chains: public formalization reference, R20, DerivativeChainPrivate.exists_chain_energy_of_step. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate

theorem DerivativeChainPrivate.exists_chain_energy_of_step
    (hstep : ∀ (P : Polynomial ℂ), 0 < P.degree → ∀ w : ℂ,
      P.derivative.eval w = 0 → ∃ v : ℂ,
        P.eval v = 0 ∧ ‖v - w‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖w‖ ^ 2)
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) (u : ℂ)
    (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      (∑ i : Fin (n - 1),
        ‖z ⟨i.val + 1, by omega⟩ - z ⟨i.val, by omega⟩‖ ^ 2) ≤
        ‖z ⟨n - 1, by omega⟩‖ ^ 2 - ‖u‖ ^ 2 := by sorry
