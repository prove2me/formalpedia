-- Prove2me | Theorems.Thm_AlonMilman1985_prop5_1_faithful
-- name    : AlonMilman1985.prop5_1_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:25:46.597478+00:00
-- url     : https://prove2.me/theorems/66b9f608-6150-42de-a6c9-3321051a98bd
-- title:
--   Proposition 5.1 — a word-length bound for finite groups from λ1 of the Cayley graph
-- statement:
--   Let $H$ be a finite group with $|H| > 1$ and $\gamma \subseteq H$ a generating set with $\gamma = \gamma^{-1}$ and $1 \in \gamma$. Let $\delta = \gamma \setminus \{1\}$, let $G(H, \delta)$ be the Cayley graph ($u \sim v$ iff $u v^{-1} \in \delta$), and let $\lambda_1$ be the second-smallest eigenvalue of its Laplacian. Then every $h \in H$ is a product $h = g_1 \cdots g_l$ of elements $g_j \in \gamma$ with
--
--   $$l \le 2\Big\lfloor \sqrt{2|\delta|/\lambda_1}\,\log_2 |H| \Big\rfloor.$$
--
--   This is Proposition 5.1 of Alon and Milman (1985): the word length $k(H,\gamma)$ is the diameter of $G(H,\delta)$, so the bound is Theorem 2.7 applied to this $|\delta|$-regular Cayley graph.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), doi:10.1016/0095-8956(85)90092-9, p. 86, Proposition 5.1

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

open Classical

theorem AlonMilman1985.prop5_1_faithful {H : Type} [Group H] [Fintype H] [DecidableEq H]
    (γ : Finset H) (hγinv : ∀ g ∈ γ, g⁻¹ ∈ γ) (h1 : (1 : H) ∈ γ)
    (hgen : Subgroup.closure (γ : Set H) = ⊤) (hn : 1 < Fintype.card H) :
    ∀ h : H, ∃ l : List H, (∀ x ∈ l, x ∈ γ) ∧ l.prod = h ∧
      l.length ≤ 2 * ⌊Real.sqrt (2 * ((γ.card - 1 : ℕ) : ℝ) /
          AlonMilman.Diameter.lambda1 (SimpleGraph.fromRel (fun u v : H => u * v⁻¹ ∈ γ))) *
        Real.logb 2 (Fintype.card H : ℝ)⌋₊ := by sorry
