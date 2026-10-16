-- Prove2me | Theorems.Thm_CompetitiveChores_IndivisibleRounding_weighted_ef11_step
-- name    : CompetitiveChores.IndivisibleRounding.weighted_ef11_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:21.138913+00:00
-- url     : https://prove2.me/theorems/7951e657-590f-4efe-b660-51daaef0f7df
-- title:
--   §7, pp. 38–39, proof of Theorem 34 — price inequalities on z′_i∖{j} and z′_{i′}∪{j′} imply (10)
-- statement:
--   The weighted-EF¹₁ step of the proof of Theorem 34.
--
--   Let $v\in\mathbb R^{n\times m}_{<0}$, $\beta\in\mathbb R^n_{>0}$, and let the indivisible allocation $z'$ be competitive at prices $p$ for some budgets $b'$. Let $i,i'$ be agents, $j\in z'_i$ and $j'\in[m]$ chores with
--
--   $$\sum_{c\in z'_i\setminus\{j\}}p_c\ \ge\ -\beta_i\qquad\text{and}\qquad\sum_{c\in z'_{i'}\cup\{j'\}}p_c\ \le\ -\beta_{i'}.$$
--
--   Then inequality (10) holds for $i,i',j,j'$:
--
--   $$\frac{u_i(z'_i\setminus\{j\})}{\beta_i}\ \ge\ \frac{u_i(z'_{i'}\cup\{j'\})}{\beta_{i'}}.$$
--
--   In the paper the two price inequalities are obtained from (12) with $b=-\beta$; then the bundle $\frac{\beta_i}{\beta_{i'}}(z'_{i'}\cup\{j'\})$ plus chore $j$ is cheaper than $z'_i$, and agent $i$'s utility maximization gives (10).
--
--   **Formalization Note** The page writes $-\beta_j$ and $\beta_i/\beta_j$ where $-\beta_{i'}$ and $\beta_i/\beta_{i'}$ are meant. The step is stated from the two price inequalities, not from (12): (12) as stated in Theorem 35 does not by itself provide $j'$ with the second inequality (see the mission's moderation notes for a three-agent instance).
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, pp. 38–39, §7, proof of Theorem 34, paragraph "For EF^1_1"

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Indivisible

namespace CompetitiveChores.IndivisibleRounding

/-- §7, pp. 38–39, proof of Theorem 34, weighted-EF¹₁ step: if the indivisible allocation `σ` is
competitive at prices `p` for some budgets `b'`, and the chores `j ∈ z_i`, `j' ∈ [m]` satisfy
`∑_{c ∈ z_i ∖ {j}} p_c ≥ −β_i` and `∑_{c ∈ z_{i'} ∪ {j'}} p_c ≤ −β_{i'}`, then inequality (10) holds:
`u_i(z_i ∖ {j}) / β_i ≥ u_i(z_{i'} ∪ {j'}) / β_{i'}`. -/
theorem weighted_ef11_step {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0)
    (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (σ : Fin m → Fin n) (b' : Fin n → ℝ) (p : Fin m → ℝ)
    (hσ : CompetitiveChores.RichFamily.IsCompetitiveWith v b' (indicator σ) p) (i i' : Fin n) (j j' : Fin m)
    (hj : j ∈ bundle σ i)
    (hi : -β i ≤ setPrice p ((bundle σ i).erase j))
    (hi' : setPrice p (insert j' (bundle σ i')) ≤ -β i') :
    setUtility v i (insert j' (bundle σ i')) / β i' ≤ setUtility v i ((bundle σ i).erase j) / β i := by sorry

end CompetitiveChores.IndivisibleRounding
