-- Prove2me | Theorems.Thm_BellSampling_Learn_determined_by_signs
-- name    : BellSampling.Learn.determined_by_signs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:51.320406+00:00
-- url     : https://prove2.me/theorems/4cc1bb99-877f-4718-8475-994c4f731d55
-- title:
--   Learning stabilizer states, p. 2 — T and the signs M|ψ⟩ = ±|ψ⟩ on a basis of T determine |ψ⟩
-- statement:
--   Let $\psi$ be an $n$-qubit stabilizer state with stabilizer set $T=T(\psi)$, and let $b_1,\dots,b_n\in T$ be linearly independent over $\mathbb F_2$ (hence a basis of $T$). For each $j$ let $M_j=(-i)^{\#\{i:(b_j)_i=11\}}\sigma_{b_j}$ be the corresponding Hermitian Pauli matrix. Then:
--   1. each $M_j$ fixes $\psi$ up to sign: $M_j|\psi\rangle=|\psi\rangle$ or $M_j|\psi\rangle=-|\psi\rangle$;
--   2. $\psi$ is determined up to a scalar by these signs: if $\varphi$ is any $n$-qubit vector with
--   $$M_j|\psi\rangle=e\,|\psi\rangle\ \Longrightarrow\ M_j|\varphi\rangle=e\,|\varphi\rangle\qquad\text{for all } j \text{ and all } e\in\mathbb C,$$
--   then $\varphi=c\,\psi$ for some $c\in\mathbb C$.
--
--   This is why learning $T$ suffices: step 5 of Algorithm 1 measures the $n$ signs, and they pin down $\psi$.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, Learning stabilizer states, "Determining T suffices to uniquely determine |ψ⟩ … to decide whether M|ψ⟩ = |ψ⟩ or M|ψ⟩ = −|ψ⟩."

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem determined_by_signs {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ)
    (b : Fin n → PStr n) (hb : ∀ j, b j ∈ stabSet ψ) (hli : LinearIndependent (ZMod 2) b) :
    (∀ j, (pauliH (b j)).mulVec ψ = ψ ∨ (pauliH (b j)).mulVec ψ = -ψ) ∧
    ∀ φ : QState n,
      (∀ j (e : ℂ), (pauliH (b j)).mulVec ψ = e • ψ → (pauliH (b j)).mulVec φ = e • φ) →
      ∃ c : ℂ, φ = c • ψ := by sorry
end BellSampling.Learn
