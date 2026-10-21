-- Prove2me | Theorems.Thm_CompetitiveChores_IndivisibleRounding_weighted_prop1_step
-- name    : CompetitiveChores.IndivisibleRounding.weighted_prop1_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:32.439117+00:00
-- url     : https://prove2.me/theorems/d404787b-2073-4cd0-b191-97026290897e
-- title:
--   §7, p. 39, proof of Theorem 34 — the price inequality on z′_i∖{j} implies (11)
-- statement:
--   The weighted-Prop1 step of the proof of Theorem 34.
--
--   Let $v\in\mathbb R^{n\times m}_{<0}$, $\beta\in\mathbb R^n_{>0}$, and let the indivisible allocation $z'$ be competitive at prices $p$ for some budgets $b'$, where the total price of all chores is $\sum_{j\in[m]}p_j=-\sum_{i'=1}^n\beta_{i'}$. Let $i$ be an agent and $j\in z'_i$ a chore with
--
--   $$\sum_{c\in z'_i\setminus\{j\}}p_c\ \ge\ -\beta_i.$$
--
--   Then inequality (11) holds for $i$ and $j$:
--
--   $$\frac{u_i(z'_i\setminus\{j\})}{\beta_i}\ \ge\ \frac{u_i([m])}{\sum_{i'=1}^n\beta_{i'}}.$$
--
--   In the paper, the bundle $\frac{\beta_i}{\sum_{i'}\beta_{i'}}[m]$ has price $-\beta_i$ because the original divisible allocation exhausts the budgets $b=-\beta$; adding chore $j$ gives a bundle cheaper than $z'_i$, and agent $i$'s utility maximization gives (11).
--
--   **Formalization Note** The page's "the price of $z'_i\setminus\{j\}$ is higher than $-\beta_i$" is read as $\ge$, matching the non-strict left inequality of (12). The total-price condition is stated as a hypothesis; it is what "the bundle has price $-\beta_i$" uses.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 39, §7, proof of Theorem 34, paragraph "To prove Prop1"

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Indivisible

namespace CompetitiveChores.IndivisibleRounding

/-- §7, p. 39, proof of Theorem 34, weighted-Prop1 step: if the indivisible allocation `σ` is
competitive at prices `p` for some budgets `b'`, the total price of all chores is `∑_j p_j = −∑_i β_i`,
and the chore `j ∈ z_i` satisfies `∑_{c ∈ z_i ∖ {j}} p_c ≥ −β_i`, then inequality (11) holds:
`u_i(z_i ∖ {j}) / β_i ≥ u_i([m]) / ∑_{i'} β_{i'}`. -/
theorem weighted_prop1_step {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0)
    (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (σ : Fin m → Fin n) (b' : Fin n → ℝ) (p : Fin m → ℝ)
    (hσ : CompetitiveChores.RichFamily.IsCompetitiveWith v b' (indicator σ) p) (hp : ∑ j, p j = -∑ i, β i) (i : Fin n)
    (j : Fin m) (hj : j ∈ bundle σ i)
    (hi : -β i ≤ setPrice p ((bundle σ i).erase j)) :
    setUtility v i Finset.univ / ∑ i', β i' ≤ setUtility v i ((bundle σ i).erase j) / β i := by sorry

end CompetitiveChores.IndivisibleRounding
