-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_remark_3_3_5
-- name    : ArrowDebreu.ThmI.remark_3_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:42:47.047109+00:00
-- url     : https://prove2.me/theorems/92d9ebe8-ab7f-40ea-aaa1-9d1d06a6decf
-- title:
--   Continuity of the truncated budget correspondence (Remark, §3.3.5)
-- statement:
--   Let an economy satisfy Assumption II, let $c \in \mathbb R$, $C = \{x : |x_h| \le c \text{ for all } h\}$, $\tilde X_i = X_i \cap C$, $\tilde Y_j = Y_j \cap C$, and let $\tilde E$ be the truncated abstract economy of §3.3.4, whose consumer $i$ faces
--   $$\tilde A_i(\bar x_i) = \Big\{x_i \in \tilde X_i : p\cdot x_i \leqq p\cdot\zeta_i + \max\Big[0, \sum_j \alpha_{ij}\, p\cdot y_j\Big]\Big\}.$$
--   Fix a consumer $i$ and suppose that $\tilde A_i(\bar x_i)$ is nonempty at every point $\bar x_i$ of the others' action space $\prod_{i' \ne i}\tilde X_{i'} \times \prod_j \tilde Y_j \times P$. Let $\bar x_i = (x_1, \dots, x_{i-1}, x_{i+1}, \dots, x_m, y_1, \dots, y_n, p)$ be such a point, and suppose
--   $$p\cdot\zeta_i > \min_{x_i \in \tilde X_i} p\cdot x_i,$$
--   i.e. some $x_i' \in \tilde X_i$ has $p\cdot x_i' < p\cdot\zeta_i$. Then $\tilde A_i$ is continuous at $\bar x_i$ in the sense of §2.4: for every $x_i^0 \in \tilde A_i(\bar x_i)$ and every sequence $\bar x_i^k \to \bar x_i$ in the others' action space there are $x_i^k \in \tilde A_i(\bar x_i^k)$ for all $k$ with $x_i^k \to x_i^0$.
--
--   This is the continuity hypothesis of the equilibrium-existence lemma for the consumers of $\tilde E$; under Assumption IV.a its condition holds at every point.
--
--   **Formalization Note** The nonemptiness of $\tilde A_i$ at every point is the fact established in §3.3.4, just before the Remark, and is taken as a hypothesis. It is needed because §2.4 asks for $x_i^k \in \tilde A_i(\bar x_i^k)$ for every $k$, not only for large $k$. The cube's half-side $c$ is an arbitrary real number.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 278 (PDF p. 15), §3.3.5, Remark

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

open AbstractEconomy

/-- **Remark (§3.3.5)**, Arrow & Debreu, Econometrica 22 (1954), p. 278 (PDF p. 15): "If
`p·ζ_i > min_{x_i ∈ X̃_i} p·x_i`, then `Ã_i(x̄_i)` is continuous at the point
`x̄_i = (x_1, ⋯, x_{i−1}, x_{i+1}, ⋯, x_m, y_1, ⋯, y_n, p)`."

Here `Ẽ = economyEtilde E c` is the truncated abstract economy of §3.3.4 (`X̃_i = X_i ∩ C`,
`Ỹ_j = Y_j ∩ C`, `C` the cube of half-side `c`), `Ã_i` its constraint set for consumer `i`, and
"continuous" is the sequential notion of §2.4 (`ConstrContinuousAt`), at a point `x̄_i` of
`𝔄̄_i` (others' actions in `X̃_{i'}`, `Ỹ_j`, `P`).

**Formalization Note.**
* The hypothesis `p·ζ_i > min_{X̃_i} p·x_i` is written `∃ x' ∈ X̃_i, p·x' < p·ζ_i`, which is
  equivalent whenever the minimum exists (`X̃_i` compact and nonempty) and needs no infimum.
* The paper's proof uses the convexity of `X̃_i` (from Assumption II) and, when it chooses
  `x_i^k = x_i` or `x_i(λ^k)` "for `k` sufficiently large", that `Ã_i` is non-null at every
  point of `𝔄̄_i` — established in §3.3.4 just before the Remark ("`Ã_i(x̄_i)` contains `x_i'` and
  therefore is non-null"). Both are hypotheses (`hne`). Without `hne` the statement is false:
  §2.4 asks for `a_i^k ∈ Ã_i(x̄_i^k)` for **all** `k`, which fails if some early `Ã_i(x̄_i^k)` is
  empty. `c` is an arbitrary real; no property of the §3.3.3 choice of `c` is used. -/
theorem remark_3_3_5 {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E) (c : ℝ) (i : Fin m)
    (hne : ∀ b, (economyEtilde E c).OthersIn (Sum.inl i) b →
      ((economyEtilde E c).constr (Sum.inl i) b).Nonempty)
    (a : Player m n → Fin l → ℝ) (ha : (economyEtilde E c).OthersIn (Sum.inl i) a)
    (hmin : ∃ x' ∈ E.X i ∩ cube l c, priceOf a ⬝ᵥ x' < priceOf a ⬝ᵥ E.ζ i) :
    (economyEtilde E c).ConstrContinuousAt (Sum.inl i) a := by sorry

end ArrowDebreu.ThmI
