-- Prove2me | Theorems.Thm_Arxiv2507_18491_chebyshev_affine_expansion
-- name    : Arxiv2507_18491.chebyshev_affine_expansion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:04:19.845005+00:00
-- url     : https://prove2.me/theorems/bd27daa8-13f4-4140-9ddd-7600df9f9334
-- title:
--   Eqs. (A.1)-(A.2): Chebyshev expansion of $T_j(ax+b)$ (as proved)
-- statement:
--   For complex constants $a,b$ and every $j\ge0$,
--   $$T_j(ax+b)=\sum_{s=0}^jC^{ab}_{js}T_s(x),$$
--   where the coefficients $C^{ab}_{js}$ are given by the recurrence (A.2):
--
--   - $C^{ab}_{00}=1$, $C^{ab}_{10}=b$, $C^{ab}_{11}=a$, $C^{ab}_{21}=4ab$;
--   - $C^{ab}_{n+1,n+1}=aC^{ab}_{nn}$ for $n\ge1$;
--   - $C^{ab}_{n+1,n}=aC^{ab}_{n,n-1}+2bC^{ab}_{nn}$ for $n\ge2$;
--   - $C^{ab}_{n+1,s}=a(C^{ab}_{n,s-1}+C^{ab}_{n,s+1})+2bC^{ab}_{ns}-C^{ab}_{n-1,s}$ for $2\le s\le n-1$, $n\ge3$;
--   - $C^{ab}_{n+1,1}=2aC^{ab}_{n0}+aC^{ab}_{n2}+2bC^{ab}_{n1}-C^{ab}_{n-1,1}$ for $n\ge2$;
--   - $C^{ab}_{n+1,0}=aC^{ab}_{n1}+2bC^{ab}_{n0}-C^{ab}_{n-1,0}$ for $n\ge1$.
--
--   **Formalization Note** Stated as proved. The printed list of initial values omits $C^{ab}_{11}$, which the recurrence uses (already in $C^{ab}_{21}=2aC^{ab}_{10}+2bC^{ab}_{11}$). The value $C^{ab}_{11}=a$ is the one forced by $T_1(ax+b)=ax+b$.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c029; Appendix A, eqs. (A.1)-(A.2), PDF p. 23

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem chebyshev_affine_expansion (a b x : ℂ) (j : ℕ) :
    chebT j (a * x + b) = ∑ s ∈ Finset.range (j + 1), chebShiftCoeff a b j s * chebT s x := by sorry

end Arxiv2507_18491
