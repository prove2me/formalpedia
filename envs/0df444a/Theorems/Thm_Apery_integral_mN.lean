-- Prove2me | Theorems.Thm_Apery_integral_mN
-- name    : Apery.integral_mN
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:20:31.608667+00:00
-- url     : https://prove2.me/theorems/e96e53ac-8794-4676-980f-9619bcbc89f2
-- title:
--   Proposition 5.1 — integrality of the normaliser $m_K$
-- statement:
--   Let $n \ge 1$, $K = 40n$, $h = 37n$, and let $m_K = \prod_{p \le 2h} p^{-L_p}$ be the normaliser whose local exponents are the proved lower bounds for $v_p^G(F_K)$ (small-prime bound (3.12), water-filling inner allocation, outer allocation; see the module `Definitions.Def_Zeta5_SourceNorm`). Then
--
--   $$m_K\,F_K \in \mathbb{Z}[X],$$
--
--   i.e. there is $Q \in \mathbb{Z}[X]$ with $Q$ mapping to $C(m_K) \cdot F_n$ in $\mathbb{Q}[X]$. This is Proposition 5.1 of the source (module `Apery/Norm.lean`, theorem `integral_mN`), proved there from the arithmetic chain `Apery/Arith/*`: every coefficient of $m_K F_K$ is $p$-integral for every prime $p$, hence an integer. **Formalization Note** The statement is exactly the source's; the normaliser `mN` and the polynomial `F` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Norm.lean#L268-L291 (statement and proof; Proposition 5.1)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceNorm

open Polynomial Finset

namespace Apery

theorem integral_mN {n : ℕ} (hn : 1 ≤ n) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (mN n) * F n := by
  sorry

end Apery
