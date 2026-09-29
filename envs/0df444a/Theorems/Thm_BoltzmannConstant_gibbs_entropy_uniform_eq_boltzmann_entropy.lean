-- Prove2me | Theorems.Thm_BoltzmannConstant_gibbs_entropy_uniform_eq_boltzmann_entropy
-- name    : BoltzmannConstant.gibbs_entropy_uniform_eq_boltzmann_entropy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:37:29.671793+00:00
-- url     : https://prove2.me/theorems/751dbc27-8068-47a9-9fec-bd8b119be135
-- title:
--   $S = k_B \log W$ for $W$ equiprobable microstates
-- statement:
--   In statistical mechanics the entropy of a system with distribution $p$ over its microstates is $S = -k_B\sum_i p_i \log p_i$. If each of the $W \ge 1$ accessible microstates is equally likely, $p_i = 1/W$, this collapses to Boltzmann's entropy formula $$S = k_B \log W,$$ the equation inscribed on Boltzmann's tombstone. The constant $k_B$ is exactly what makes the statistical-mechanical entropy agree with the classical thermodynamic entropy of Clausius.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Role in the statistical definition of entropy" ($S = k \log W$) and section "Natural units" (equiprobable microstates)

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem gibbs_entropy_uniform_eq_boltzmann_entropy {ι : Type*} (s : Finset ι) (W : ℕ)
    (hW : s.card = W) (hW0 : 0 < W) :
    gibbsEntropy s (fun _ => 1 / (W : ℝ)) = boltzmannEntropy W := by sorry

end BoltzmannConstant
