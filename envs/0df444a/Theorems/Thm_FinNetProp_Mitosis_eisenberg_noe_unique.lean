-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_eisenberg_noe_unique
-- name    : FinNetProp.Mitosis.eisenberg_noe_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:38.603984+00:00
-- url     : https://prove2.me/theorems/d998a4c6-2d4a-46bb-8854-90d4f270a753
-- title:
--   §2, after Definition 2.2, p. 2801 — the system (2.1) has a unique solution (Eisenberg–Noe 2001, Theorem 2)
-- statement:
--   Let $F = (N, z, L)$ be a financial network: $N$ a nonempty finite set of agents, endowments $z_i > 0$, and a nonnegative liability matrix $L$ with zero diagonal. Write $\Pi$ for its relative liability matrix. Then there is exactly one payment matrix $P \in \mathcal M(N)$ (nonnegative, zero diagonal) such that
--   $$P_{ij} = \min\Big\{\Pi_{ij}\Big(z_i + \sum_{k \in N} P_{ki}\Big),\ L_{ij}\Big\}, \qquad i, j \in N. \tag{2.1}$$
--
--   The paper takes this from Theorem 2 of Eisenberg and Noe (2001); it is what makes the proportional rule $p$ a well-defined bankruptcy rule, and its uniqueness part is used again in the continuity step of Theorem 4.2.
--
--   **Formalization Note** Strict positivity of the endowments (the page's $z \in \mathbb R^N_{++}$) is built into the network structure and is needed: with zero endowments two agents owing each other $1$ admit both $P = 0$ and $P = L$. Matrices are functions on $\mathbb N \times \mathbb N$ that vanish outside $N \times N$, so uniqueness is uniqueness of that function.
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, p. 2801, sentence after Definition 2.2 ('It follows from theorem 2 in Eisenberg and Noe (2001) that the system of equations (2.1) has a unique solution.')

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

theorem eisenberg_noe_unique (F : FinNet) : ∃! P : ℕ → ℕ → ℝ, IsPropSolution F P := by sorry

end FinNetProp.Mitosis
