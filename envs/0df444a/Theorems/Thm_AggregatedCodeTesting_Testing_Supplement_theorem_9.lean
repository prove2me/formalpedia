-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_Supplement_theorem_9
-- name    : AggregatedCodeTesting.Testing.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:30:01.097105+00:00
-- url     : https://prove2.me/theorems/5ec8ce5d-bca9-47b1-b034-b3e1ec1b5612
-- title:
--   Theorem 9 — worst testing exponent
-- statement:
--   Fix a binary linear code $C\le\mathbb F_2^m$ without identically zero coordinates, with $S=s^*(C)>0$. The order $S$ is finite. There are positive constants $K_C,c_C$ and a positive integer $w_0(C)$ such that every width $w\ge1$ and every distinct-profile pair $\ell,\ell'$ admit a randomized test with both errors at most $1/4$ using an integer $N$ satisfying
--
--   $$N\le K_Cw^S.$$
--
--   For every $w\ge w_0(C)$ there exist $\ell,\ell'$ with distinct block-coset profiles such that every randomized test with both errors at most $1/4$ needs
--
--   $$N\ge c_Cw^S.$$
--
--   The hard pair is allowed to depend on the width; the lower bound holds at every sufficiently large width. All constants are fixed after the code and before widths, profiles and tests. The theorem concerns the full observation law, allows decomposable codes and makes no density or parity restriction on the upper bound.
--
--   Differences from the source:
--   - encoding: O_C and Omega_C bounds for minimum sample count → positive code-only constants with an integer test witness for the upper bound and every admissible randomized test for the lower bound; reason: these are equivalent operational statements using the published CanTest and its error target 1/4
--   - encoding: finite detection exponent S → finiteness is concluded and the natural value of sStar is then used in powers; reason: no finiteness property is assumed as an additional hypothesis
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 9, printed p.8 (PDF p.9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf; pinned PDF SHA256 1f5fce093155b2721073a124d87a3c6947269ff7851c61301dfa6e81232f0b2c

import Definitions.Def_AggregatedCodeTesting_Testing_Orders
import Definitions.Def_AggregatedCodeTesting_Testing_HypothesisTesting

set_option autoImplicit false

namespace AggregatedCodeTesting.Testing.Supplement

/-- Theorem 9, printed p.8 / PDF p.9. Uniform upper and every sufficiently large width lower. -/
theorem theorem_9 {m : ℕ} (C : Submodule (ZMod 2) (Word m))
    (hC : HasNoZeroCoord C) (hS : 0 < sStar C) :
    sStar C ≠ ⊤ ∧
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∃ w0 : ℕ, 1 ≤ w0 ∧
      (∀ w : ℕ, 1 ≤ w → ∀ l l' : Fin w → Word m, profile C l ≠ profile C l' →
        ∃ N : ℕ, (N : ℝ) ≤ K * (w : ℝ) ^ (sStar C).toNat ∧
          CanTest (law C l) (law C l') N (1 / 4)) ∧
      (∀ w : ℕ, w0 ≤ w → ∃ l l' : Fin w → Word m,
        profile C l ≠ profile C l' ∧
        ∀ N : ℕ, CanTest (law C l) (law C l') N (1 / 4) →
          c * (w : ℝ) ^ (sStar C).toNat ≤ (N : ℝ)) := by sorry

end AggregatedCodeTesting.Testing.Supplement
