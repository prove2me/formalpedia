-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_tail_energy
-- name    : DerivativeChainContinuation.finite_tail_energy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:55:52.503042+00:00
-- url     : https://prove2.me/theorems/6aa03b3f-4ebb-478b-9699-314c0c8e7808
-- title:
--   A finite derivative tail admits a telescoping square-cost bound
-- statement:
--   Let $h\in\mathbb N$ and let $P_j\in\mathbb C[X]$ be indexed by $j\in\mathbb N$. For $j<h$, suppose $P_{j+1}$ has positive degree and each root of $P_j$ is a root of $P_{j+1}^{\prime}$. From any root $b$ of $P_0$, one can choose roots $z_j$ of $P_j$ for $0\le j\le h$ with
--
--   $$z_0=b,\qquad \sum_{j=0}^{h-1}|z_{j+1}-z_j|^2\le |z_h|^2-|b|^2.$$
--
--   No disk or simple-root hypothesis is imposed. This is the finite energy tail used after a sparse prefix.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteTailEnergy.lean#L7-L39

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



end DerivativeChainContinuation

theorem DerivativeChainContinuation.finite_tail_energy (P : ℕ → Polynomial ℂ) (h : ℕ)
    (hdegree : ∀ j < h, 0 < (P (j+1)).degree)
    (hstep : ∀ j < h, ∀ w : ℂ, (P j).eval w=0 → (P (j+1)).derivative.eval w=0)
    (b : ℂ) (hb : (P 0).eval b=0) :
    ∃ z : ℕ → ℂ, z 0=b ∧ (∀ j ≤ h, (P j).eval (z j)=0) ∧
      (∑ j ∈ Finset.range h, ‖z (j+1)-z j‖^2) ≤ ‖z h‖^2-‖b‖^2 := by sorry
