-- Prove2me | Theorems.Thm_DrezetGHZ_local_model_reproducing_ghz_is_deterministic
-- name    : DrezetGHZ.local_model_reproducing_ghz_is_deterministic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T20:44:19.964855+00:00
-- url     : https://prove2.me/theorems/e2926420-8bc1-464e-9f72-9f2c88e9582c
-- title:
--   Section II (ii): a locally causal model reproducing GHZ is almost surely deterministic
-- statement:
--   Let $M$ be a locally causal model on a measurable space $\Lambda$, with setting-independent probability measure $\rho$ and local responses $P_j(\alpha\mid\lambda,\hat n)$. Suppose $M$ reproduces the GHZ Born probabilities for all outcomes in each of the four settings $(\hat x,\hat x,\hat x)$, $(\hat x,\hat y,\hat y)$, $(\hat y,\hat x,\hat y)$, $(\hat y,\hat y,\hat x)$.
--
--   Then for $\rho$-almost every $\lambda$ there are values $A_1,A_2,A_3,B_1,B_2,B_3\in\{\pm1\}$ such that
--   $$P_j(\alpha\mid\lambda,\hat x)=\delta_{\alpha,A_j},\qquad P_j(\alpha\mid\lambda,\hat y)=\delta_{\alpha,B_j}\qquad(j=1,2,3),$$
--   and
--   $$A_1A_2A_3=-1,\quad A_1B_2B_3=+1,\quad B_1A_2B_3=+1,\quad B_1B_2A_3=+1.$$
--
--   This is Eq. (27) together with the GHZ constraints (10)–(13), established for almost every beable.
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, p. 7, Eq. (27) and summary point (ii): "for the GHZ state, locality added to quantum mechanics implies determinism"; together with Eqs. (10)–(13) on p. 4.

import Mathlib
import Definitions.Def_DrezetGHZ_Models
open MeasureTheory

namespace DrezetGHZ
theorem local_model_reproducing_ghz_is_deterministic {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ)
    (hxxx : ∀ α β γ : ℤˣ, M.predict .x .x .x α β γ = bornProb .x .x .x α β γ)
    (hxyy : ∀ α β γ : ℤˣ, M.predict .x .y .y α β γ = bornProb .x .y .y α β γ)
    (hyxy : ∀ α β γ : ℤˣ, M.predict .y .x .y α β γ = bornProb .y .x .y α β γ)
    (hyyx : ∀ α β γ : ℤˣ, M.predict .y .y .x α β γ = bornProb .y .y .x α β γ) :
    ∀ᵐ lam ∂M.ρ, ∃ A B : Fin 3 → ℤˣ,
      (∀ j α, M.P j lam .x α = if α = A j then 1 else 0) ∧
      (∀ j α, M.P j lam .y α = if α = B j then 1 else 0) ∧
      A 0 * A 1 * A 2 = -1 ∧
      A 0 * B 1 * B 2 = 1 ∧
      B 0 * A 1 * B 2 = 1 ∧
      B 0 * B 1 * A 2 = 1 := by sorry
end DrezetGHZ
