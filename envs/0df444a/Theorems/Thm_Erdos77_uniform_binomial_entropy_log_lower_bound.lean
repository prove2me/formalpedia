-- Prove2me | Theorems.Thm_Erdos77_uniform_binomial_entropy_log_lower_bound
-- name    : Erdos77.uniform_binomial_entropy_log_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T14:15:58.04863+00:00
-- url     : https://prove2.me/theorems/210a633e-eee3-44a6-9f59-78e656ce121f
-- title:
--   Binomial entropy bound with logarithmic loss
-- statement:
--   For positive integers ell ? k, the binomial coefficient choose(k+ell, ell) is at least the exponential of the binary entropy term k((1+ell/k) log(1+ell/k) ? (ell/k) log(ell/k)), with a uniform logarithmic loss log(2k+1). The bound follows by considering the ell-th mass of the binomial distribution with success probability ell/(k+ell): this mass is a mode, hence at least 1/(k+ell+1), and k+ell+1 ? 2k+1.
-- source:
--   The standard entropy lower bound for binomial coefficients, obtained from the binomial distribution; this is the explicit O(log k) form underlying Erdos77.uniform_binomial_entropy_lower_bound.

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey
open Filter Topology

namespace Erdos77
theorem uniform_binomial_entropy_log_lower_bound :
  forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
    Real.exp ((((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
      ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) -
      Real.log (2 * (k : Real) + 1)) <= (Nat.choose (k + ell) ell : Real) := by sorry
end Erdos77
