-- Prove2me | Theorems.Thm_DesignTest_mub_exists_prime_power
-- name    : DesignTest.mub_exists_prime_power
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:29.810292+00:00
-- url     : https://prove2.me/theorems/3a0dbfdc-20b8-41d8-8625-ece908a2020e
-- title:
--   [WF89], cited in the proof of Cor. 4.17 — $d+1$ mutually unbiased bases exist in every prime-power dimension $d$
-- statement:
--   For every prime power $d=p^k$ ($p$ prime, $k\ge1$) there is a complete set of mutually unbiased bases of $\mathbb C^d$: orthonormal bases $B_0,\dots,B_d$ with
--   $$|\langle b|b'\rangle|^2=\frac1d\qquad\text{for } b\in B_r,\ b'\in B_s,\ r\ne s .$$
--
--   This is the result of Wootters and Fields (1989) that the paper cites to obtain a uniform exact state $2$-design on $d(d+1)$ states in prime-power dimensions.
--
--   **Formalization Note** `IsPrimePow d` is Mathlib's predicate $\exists p\,k,\ p\text{ prime}\wedge k>0\wedge p^k=d$; the bases are families of unit vectors that are orthonormal in $\mathbb C^d$.
--
--   Differences from the source:
--   - encoding: d + 1 mutually unbiased orthonormal bases of ℂ^d → B : Fin (d + 1) → Fin d → PureVec d with IsMUBFamily B (each B r orthonormal, |⟨B r i | B s j⟩|² = 1/d for r ≠ s); reason: the standard definition of a complete set of mutually unbiased bases
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), proof of Corollary 4.17, p.44 (Wootters–Fields [WF89], Ann. Physics 191 (1989) 363–381)

import Mathlib
import Definitions.Def_DesignTest_IsMUBFamily

set_option autoImplicit false

namespace DesignTest

/-- **Complete sets of mutually unbiased bases in prime-power dimension** [Wootters–Fields 1989], as cited
in A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission
(sha256 e2f0a429…), proof of Corollary 4.17, p.44.

For every prime power `d = p^k` (`p` prime, `k ≥ 1`) there are `d + 1` orthonormal bases of `ℂ^d` that are
pairwise mutually unbiased: `|⟨b|b'⟩|² = 1/d` for `b, b'` from different bases.

**Formalization Note.** `IsPrimePow d` is Mathlib's predicate `∃ p k, p prime ∧ 0 < k ∧ p^k = d`. -/
theorem mub_exists_prime_power (d : ℕ) (hd : IsPrimePow d) :
    ∃ B : Fin (d + 1) → Fin d → PureVec d, IsMUBFamily B := by sorry

end DesignTest
