-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_root_histories
-- name    : DerivativeChainContinuation.finite_root_histories
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:20:17.910724+00:00
-- url     : https://prove2.me/theorems/9b35de7f-e558-4047-817d-f74fd98a7805
-- title:
--   Actual derivative transitions admit a finite mean-preserving history law
-- statement:
--   Let $P_j\in\mathbb C[X]$ and $h\in\mathbb N$. For each $j<h$, assume $P_{j+1}$ has positive degree and every root of $P_j$ is critical for $P_{j+1}$. Start with a finite probability law $\pi_i$ on roots $b_i$ of $P_0$, with mean $u\in\mathbb C$ and $|b_i-u|^2=\rho^2$ for $\rho\in\mathbb R$. There is a finite probability law on compatible root histories $z$ that preserves the initial atoms, has final mean $u$, and satisfies
--
--   $$\mathbb E\,E_h(z)=\mathbb E|z(h)-u|^2-\rho^2,\qquad E_h(z)=\sum_{j<h}|z(j+1)-z(j)|^2.$$
--
--   The proof constructs the finite transition law from the actual polynomial roots, including repeated roots.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteRootHistories.lean#L12-L98

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators





end DerivativeChainContinuation

theorem DerivativeChainContinuation.finite_root_histories {ι : Type} [Fintype ι]
    (P : ℕ → Polynomial ℂ) (h : ℕ)
    (hdegree : ∀ k < h, 0 < (P (k+1)).degree)
    (hstep : ∀ k < h, ∀ w : ℂ, (P k).eval w=0 → (P (k+1)).derivative.eval w=0)
    (π : ι → ℝ) (b : ι → ℂ) (u : ℂ) (ρ : ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i=1)
    (hπmean : ∑ i, (π i:ℂ)*b i=u) (hb : ∀ i, (P 0).eval (b i)=0)
    (hρ : ∀ i, ‖b i-u‖^2=ρ^2) :
    ∃ (κ : Type) (inst : Fintype κ), letI := inst;
      ∃ (w : κ → ℝ) (z : κ → ℕ → ℂ) (origin : κ → ι),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧ (∀ i, z i 0=b (origin i)) ∧
        (∀ i k, k ≤ h → (P k).eval (z i k)=0) ∧
        (∑ i, (w i:ℂ)*z i h=u) ∧
        (∑ i, w i*historyEnergy h (z i))=(∑ i, w i*‖z i h-u‖^2)-ρ^2 := by sorry
