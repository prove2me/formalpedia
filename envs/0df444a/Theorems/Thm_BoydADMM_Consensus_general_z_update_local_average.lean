-- Prove2me | Theorems.Thm_BoydADMM_Consensus_general_z_update_local_average
-- name    : BoydADMM.Consensus.general_z_update_local_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:35.033983+00:00
-- url     : https://prove2.me/theorems/6b850498-cbcd-49fa-9b61-1d7fedd28417
-- title:
--   §7.2: the general form consensus $z$-update is local averaging
-- statement:
--   Consider general form consensus (§7.2) with the index map $\mathcal G$, $\rho>0$, and assume every global entry is copied at least once: $k_g=\#\{(i,j):\mathcal G(i,j)=g\}\ge1$ for every $g$. Fix $x_i\in\mathbb R^{n_i}$ (standing for $x_i^{k+1}$) and $y_i\in\mathbb R^{n_i}$ (standing for $y_i^k$). Then $z\in\mathbb R^n$ minimizes
--   $$\sum_{i=1}^N\big(-y_i^{T}\tilde z_i+(\rho/2)\|x_i-\tilde z_i\|_2^2\big)$$
--   if and only if, for every global index $g$,
--   $$z_g=\frac{\sum_{\mathcal G(i,j)=g}\big((x_i)_j+(1/\rho)(y_i)_j\big)}{\sum_{\mathcal G(i,j)=g}1}.$$
--
--   So each global entry is the average of the local entries $x_i+(1/\rho)y_i$ that copy it.
--
--   **Formalization Note** The book writes the sum in the $z$-update as $\sum_{i=1}^m$; $m$ is a typo for $N$. The hypothesis $k_g\ge1$ is implicit in the book (otherwise $z_g$ does not appear in the objective and the formula divides by zero). Indices are 0-based in Lean.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 55, §7.2 (z-update of general form consensus ADMM; the book prints ∑_{i=1}^m for ∑_{i=1}^N)

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- §7.2, p. 55: in general form consensus, if every global component is copied at least once
(`k_g ≥ 1` for every `g`), then `z` minimizes the `z`-update objective
`∑_i (−y_i^{kT} z̃_i + (ρ/2)‖x_i^{k+1} − z̃_i‖²)` over `z ∈ ℝⁿ` iff every component is the local
average `z_g = ∑_{G(i,j)=g} ((x_i^{k+1})_j + (1/ρ)(y_i^k)_j) / k_g`. Here `x`, `y` stand for
`x^{k+1}`, `y^k`. -/
theorem general_z_update_local_average {n N : ℕ} {nl : Fin N → ℕ}
    (G : (i : Fin N) → Fin (nl i) → Fin n) (hG : ∀ g, 1 ≤ kg G g) (ρ : ℝ) (hρ : 0 < ρ)
    (x y : (i : Fin N) → EuclideanSpace ℝ (Fin (nl i))) (z : EuclideanSpace ℝ (Fin n)) :
    (∀ z' : EuclideanSpace ℝ (Fin n),
        ∑ i, (-⟪y i, ztil G z i⟫_ℝ + (ρ / 2) * ‖x i - ztil G z i‖ ^ 2) ≤
          ∑ i, (-⟪y i, ztil G z' i⟫_ℝ + (ρ / 2) * ‖x i - ztil G z' i‖ ^ 2)) ↔
      ∀ g, z g = (∑ p ∈ entriesOf G g, (x p.1 p.2 + (1 / ρ) * y p.1 p.2)) / (kg G g : ℝ) := by sorry

end BoydADMM.Consensus
