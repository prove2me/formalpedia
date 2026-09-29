-- Prove2me | Theorems.Thm_BoltzmannConstant_rescaled_entropy_eq_shannon
-- name    : BoltzmannConstant.rescaled_entropy_eq_shannon
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:41:58.357178+00:00
-- url     : https://prove2.me/theorems/124833ad-68c1-4c0b-9966-b90f4a0db853
-- title:
--   The rescaled entropy $S/k_B$ is the Shannon entropy
-- statement:
--   Dividing the thermodynamic entropy by $k_B$ gives a dimensionless quantity $$S' = S/k_B = -\sum_i p_i \log p_i,$$ which is exactly Shannon's information entropy measured in nats. In other words, the Boltzmann constant is precisely the conversion factor between information-theoretic entropy and thermodynamic entropy; in natural units where $k_B = 1$ the two coincide.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Role in the statistical definition of entropy" (rescaled dimensionless entropy corresponding exactly to Shannon's information entropy) and section "Natural units"

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem rescaled_entropy_eq_shannon {ι : Type*} (s : Finset ι) (p : ι → ℝ) :
    gibbsEntropy s p / kB = shannonEntropy s p := by sorry

end BoltzmannConstant
