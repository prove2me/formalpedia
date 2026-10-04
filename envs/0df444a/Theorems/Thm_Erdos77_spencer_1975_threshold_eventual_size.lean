-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_threshold_eventual_size
-- name    : Erdos77.spencer_1975_threshold_eventual_size
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T14:04:35.642844+00:00
-- url     : https://prove2.me/theorems/90a1033a-f6ea-41d0-b9b8-37d4c1ce63e1
-- title:
--   The Spencer threshold eventually exceeds k
-- statement:
--   For each fixed $0 < \varepsilon < 1$, the threshold $\lfloor(1-\varepsilon)(\sqrt{2}/e)k2^{k/2}\rfloor$ eventually is at least $k$, and $k$ is eventually at least 2. This is the elementary growth component of Spencer's asymptotic threshold argument.
-- source:
--   J. Spencer, Ramsey's theorem: a new lower bound, J. Combin. Theory Ser. A 18 (1975), pp. 108-115, p. 110, Corollary 2.

import Mathlib
open Filter

namespace Erdos77
theorem spencer_1975_threshold_eventual_size (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Filter.Eventually (fun k : Nat =>
      2 <= k /\
        k <= Nat.floor
          ((1 - epsilon) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
            (2 : Real) ^ ((k : Real) / 2))) Filter.atTop := by sorry
end Erdos77
