-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_theorem_I
-- name    : ArrowDebreu.ThmI.theorem_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:44:23.434999+00:00
-- url     : https://prove2.me/theorems/6f936c65-a456-4a85-b2ae-c676464d53c7
-- title:
--   Theorem I of Arrow–Debreu (1954): existence of a competitive equilibrium
-- statement:
--   Consider an economy with $l \ge 1$ commodities, $n$ production units with production sets $Y_j \subseteq \mathbb R^l$, and $m$ consumption units with consumption sets $X_i \subseteq \mathbb R^l$, utilities $u_i$, initial holdings $\zeta_i$ and profit shares $\alpha_{ij}$. Suppose Assumptions I–IV hold:
--
--   1. (I) each $Y_j$ is closed, convex and contains $0$; $Y \cap \Omega = \{0\}$ and $Y \cap (-Y) = \{0\}$ for $Y = \sum_j Y_j$ and $\Omega$ the nonnegative orthant;
--   2. (II) each $X_i$ is closed, convex and bounded from below;
--   3. (III) each $u_i$ is continuous on $X_i$, has no satiation point in $X_i$, and satisfies $u_i[t x_i + (1-t)x_i'] > u_i(x_i')$ whenever $u_i(x_i) > u_i(x_i')$ and $0 < t < 1$;
--   4. (IV) each consumer can consume some $x_i \in X_i$ with $x_i < \zeta_i$ in every component; $\alpha_{ij} \ge 0$ and $\sum_i \alpha_{ij} = 1$.
--
--   Then there is a **competitive equilibrium**: vectors $x_1^*, \dots, x_m^*$, $y_1^*, \dots, y_n^*$ and $p^*$ such that each $y_j^*$ maximizes profit $p^*\cdot y_j$ over $Y_j$, each $x_i^*$ maximizes $u_i$ over the budget set $\{x_i \in X_i : p^*\cdot x_i \leqq p^*\cdot\zeta_i + \sum_j \alpha_{ij}\, p^*\cdot y_j^*\}$, $p^* \geqq 0$ with $\sum_h p^*_h = 1$, and
--   $$z^* = \sum_i x_i^* - \sum_j y_j^* - \sum_i \zeta_i \leqq 0, \qquad p^*\cdot z^* = 0.$$
--
--   This is the first general existence theorem for a competitive equilibrium with production, and the foundation of the Arrow–Debreu model of general equilibrium.
--
--   **Formalization Note** $l \ge 1$ is stated explicitly; for $l = 0$ the price simplex is empty and the statement would fail for the economy with no agents.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 272 (PDF p. 9), §1.5.1, Theorem I

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **Theorem I (§1.5.1)**, Arrow & Debreu, *Existence of an Equilibrium for a Competitive
Economy*, Econometrica 22 (1954), p. 272 (PDF p. 9): "For any economic system satisfying
Assumptions I–IV, there is a competitive equilibrium."

For every economy with `l ≥ 1` commodities, `m` consumption units and `n` production units that
satisfies Assumptions I.a–I.c, II, III.a–III.c and IV.a–IV.b, there are consumption vectors
`x_i^*`, production plans `y_j^*` and a price vector `p^*` satisfying Conditions 1–4
(Definition 1.5.0).

**Formalization Note.** `0 < l` is added: with `l = 0` the price simplex
`P = {p ≧ 0 | Σ_h p_h = 1}` is empty, and for `m = n = 0` all of Assumptions I–IV hold while no
competitive equilibrium exists. The paper takes `l ≥ 1` for granted. -/
theorem theorem_I {l m n : ℕ} (hl : 0 < l) (E : Economy l m n) (hE : AssumptionsItoIV E) :
    ∃ (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ) (p : Fin l → ℝ),
      IsCompetitiveEquilibrium E x y p := by sorry

end ArrowDebreu.ThmI
