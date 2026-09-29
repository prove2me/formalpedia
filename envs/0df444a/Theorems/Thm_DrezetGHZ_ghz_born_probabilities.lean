-- Prove2me | Theorems.Thm_DrezetGHZ_ghz_born_probabilities
-- name    : DrezetGHZ.ghz_born_probabilities
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T19:44:02.623409+00:00
-- url     : https://prove2.me/theorems/3adefea7-a750-4fc1-8080-c3e80ee60dcb
-- title:
--   GHZ Born probabilities for the four GHZ settings
-- statement:
--   For every triple of outcomes $\alpha,\beta,\gamma\in\{\pm1\}$, the Born probabilities of the GHZ state are
--   $$P(\alpha,\beta,\gamma\mid\hat x,\hat x,\hat x,\psi)=\begin{cases}\tfrac14&\alpha\beta\gamma=-1\\0&\text{otherwise,}\end{cases}$$
--   and, for each of the settings $(\hat x,\hat y,\hat y)$, $(\hat y,\hat x,\hat y)$ and $(\hat y,\hat y,\hat x)$,
--   $$P(\alpha,\beta,\gamma\mid\hat n_1,\hat n_2,\hat n_3,\psi)=\begin{cases}\tfrac14&\alpha\beta\gamma=+1\\0&\text{otherwise.}\end{cases}$$
--
--   So in each GHZ experiment exactly four of the $2^3$ outcome triples occur, each with probability $1/4$.
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, p. 10 (after Eq. (29): $|A_{\alpha,\beta,\gamma}|^2=1/4$ iff $\alpha\beta\gamma=-1$), p. 11 (after Eq. (32): $|B_{\alpha,\beta,\gamma}|^2=1/4$ iff $\alpha\beta\gamma=+1$), and p. 13 (four possible triplets per GHZ game).

import Mathlib
import Definitions.Def_DrezetGHZ_Quantum

namespace DrezetGHZ
theorem ghz_born_probabilities (α β γ : ℤˣ) :
    bornProb .x .x .x α β γ = (if α * β * γ = -1 then 1 / 4 else 0) ∧
    bornProb .x .y .y α β γ = (if α * β * γ = 1 then 1 / 4 else 0) ∧
    bornProb .y .x .y α β γ = (if α * β * γ = 1 then 1 / 4 else 0) ∧
    bornProb .y .y .x α β γ = (if α * β * γ = 1 then 1 / 4 else 0) := by sorry
end DrezetGHZ
