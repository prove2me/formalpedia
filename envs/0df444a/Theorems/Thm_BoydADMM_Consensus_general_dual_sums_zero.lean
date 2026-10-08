-- Prove2me | Theorems.Thm_BoydADMM_Consensus_general_dual_sums_zero
-- name    : BoydADMM.Consensus.general_dual_sums_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:40.135518+00:00
-- url     : https://prove2.me/theorems/72d5b45e-8180-4b88-909f-f30b4b1cc485
-- title:
--   §7.2: after the first iteration $\sum_{\mathcal G(i,j)=g}(y_i^k)_j=0$ and $z_g^{k+1}=(1/k_g)\sum_{\mathcal G(i,j)=g}(x_i^{k+1})_j$
-- statement:
--   Let $x_i^k, z^k, y_i^k$ be any run of general form consensus ADMM (§7.2) with $\rho>0$, and assume $k_g\ge1$ for every global index $g$. Then, for every $k\ge1$ and every $g$:
--
--   1. the dual entries attached to $g$ sum to zero:
--   $$\sum_{\mathcal G(i,j)=g}(y_i^k)_j=0;$$
--   2. the $z$-update is plain local averaging:
--   $$z_g^{k+1}=\frac1{k_g}\sum_{\mathcal G(i,j)=g}(x_i^{k+1})_j.$$
--
--   **Formalization Note** "After the first iteration" is read as $k\ge1$ (the run starts at an arbitrary $y^0$). The hypothesis $k_g\ge1$ is implicit in the book. The run's $z$-update is the argmin of the page's $z$-objective, so item 2 is derived, not assumed.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 55, §7.2 (∑_{𝒢(i,j)=g} (y_i^k)_j = 0 after the first iteration; simplified z-update)

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- §7.2, p. 55: along every run of general form consensus ADMM with `ρ > 0` and every
`k_g ≥ 1`, after the first iteration (`k ≥ 1`) the dual entries attached to each global index
sum to zero, `∑_{G(i,j)=g} (y_i^k)_j = 0`, and the `z`-update is plain local averaging,
`z_g^{k+1} = (1/k_g) ∑_{G(i,j)=g} (x_i^{k+1})_j`. -/
theorem general_dual_sums_zero {n N : ℕ} {nl : Fin N → ℕ}
    (G : (i : Fin N) → Fin (nl i) → Fin n) (hG : ∀ g, 1 ≤ kg G g) (ρ : ℝ) (hρ : 0 < ρ)
    (Cf : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (nl i))))
    (f : (i : Fin N) → EuclideanSpace ℝ (Fin (nl i)) → ℝ)
    (x : ℕ → (i : Fin N) → EuclideanSpace ℝ (Fin (nl i))) (z : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → (i : Fin N) → EuclideanSpace ℝ (Fin (nl i)))
    (hrun : IsGeneralConsensusADMMRun G Cf f ρ x z y) :
    (∀ k, 1 ≤ k → ∀ g, ∑ p ∈ entriesOf G g, y k p.1 p.2 = 0) ∧
    (∀ k, 1 ≤ k → ∀ g,
      z (k + 1) g = (1 / (kg G g : ℝ)) * ∑ p ∈ entriesOf G g, x (k + 1) p.1 p.2) := by sorry

end BoydADMM.Consensus
