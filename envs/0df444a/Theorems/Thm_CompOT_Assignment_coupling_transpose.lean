-- Prove2me | Theorems.Thm_CompOT_Assignment_coupling_transpose
-- name    : CompOT.Assignment.coupling_transpose
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:59.182968+00:00
-- url     : https://prove2.me/theorems/25a135f5-4b87-42f7-996a-1f65b4b8dba3
-- title:
--   §2.3, p. 371 — transposing a coupling swaps its marginals
-- statement:
--   A matrix $P$ transports the histogram $a$ to $b$ exactly when its transpose transports $b$ to $a$:
--
--   $$P\in U(a,b)\quad\Longleftrightarrow\quad P^{\mathsf T}\in U(b,a).$$
--
--   This symmetry is useful when comparing transport problems with their source and target roles reversed.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §2.3, p. 371, paragraph after (2.10)

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

theorem coupling_transpose {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    P ∈ couplings a b ↔ P.transpose ∈ couplings b a := by sorry

end CompOT.Assignment
