-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_Supplement_theorem_5
-- name    : AggregatedCodeTesting.Testing.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:29:24.963661+00:00
-- url     : https://prove2.me/theorems/3994346e-7585-4219-bfef-f67af1bd57bb
-- title:
--   Theorem 5 — explicit infinite rank-three family
-- statement:
--   For every integer $k\ge1$, put $m=k+4$, $\alpha=1100\,0^k$, $\beta=0011\,0^k$, $\gamma=1010\,1^k$, $D_k=\langle\alpha,\beta,\gamma\rangle$ and $C_k=D_k^\perp$. Then $C_k$ is indecomposable, has no identically zero coordinate, and $\dim C_k^\perp=3$. The character $A=\alpha+\beta=1111\,0^k$ satisfies
--
--   $$|A|=4,\qquad t_{C_k}(A)=2k+4=2m-4=s^*(C_k).$$
--
--   Every coefficient of $L_A$ below degree $2k+4$ is zero, and its entire homogeneous part at that degree is
--
--   $$-2z_1z_2z_3z_4\prod_{i=5}^m z_i^2.$$
--
--   This gives unbounded detection delay at fixed character weight and dual dimension. There is no upper bound on $k$.
--
--   Differences from the source:
--   - encoding: coordinates 1 through m → coordinates Fin m numbered 0 through m-1; reason: the index bijection preserves every generator and tail exponent
--   - encoding: dimension of the binary dual and lowest homogeneous part → finrank of the actual orthogonal submodule and coefficientwise rational formal-series equality; reason: this states the entire dimension and polynomial claims without identifying the leading part by a single selected coefficient
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 5, printed p.5 (PDF p.6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf; pinned PDF SHA256 1f5fce093155b2721073a124d87a3c6947269ff7851c61301dfa6e81232f0b2c

import Definitions.Def_AggregatedCodeTesting_Testing_Supplement_Algebra

set_option autoImplicit false
open Finset

namespace AggregatedCodeTesting.Testing.Supplement

/-- Theorem 5, printed p.5 / PDF p.6, including every coefficient of the first homogeneous part. -/
theorem theorem_5 (k : ℕ) (hk : 1 ≤ k) :
    IsIndecomposable (familyCode k) ∧
    HasNoZeroCoord (familyCode k) ∧
    Module.finrank (ZMod 2) (orthogonal (familyCode k)) = 3 ∧
    weight (familyCharacter k) = 4 ∧
    detOrder (familyCode k) univ (familyCharacter k) = (2 * k + 4 : ℕ) ∧
    (2 * k + 4 : ℕ) = 2 * (k + 4) - 4 ∧
    sStar (familyCode k) = (2 * k + 4 : ℕ) ∧
    (∀ v : Fin (k + 4) →₀ ℕ, v.degree < 2 * k + 4 →
      MvPowerSeries.coeff v (logChar (familyCode k) univ (familyCharacter k)) = 0) ∧
    (∀ v : Fin (k + 4) →₀ ℕ, v.degree = 2 * k + 4 →
      MvPowerSeries.coeff v (logChar (familyCode k) univ (familyCharacter k)) =
        if v = familyExponent k then -2 else 0) := by sorry

end AggregatedCodeTesting.Testing.Supplement
