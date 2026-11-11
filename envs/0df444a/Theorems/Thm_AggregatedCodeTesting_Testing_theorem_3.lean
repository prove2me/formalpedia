-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_theorem_3
-- name    : AggregatedCodeTesting.Testing.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:58.425321+00:00
-- url     : https://prove2.me/theorems/04af323c-4c99-4757-be30-a082a52c01fd
-- title:
--   Theorem 3 — character formula: parity of monomials, finite detection orders, cumulant criterion and $s(\ell,\ell')=\min t_C(A)$
-- statement:
--   Let $C\le\mathbb F_2^m$ be a binary linear code without identically zero coordinates. For an informative block $D$, a character $0\ne A\in C_D^\perp$ and $L_A(z)=q^{-1}\sum_\sigma\chi_A(\sigma)\log g_\sigma(z)$ with detection order $t_{C_D}(A)$:
--
--   1. every monomial $z^v$ of $L_A$ has $v\equiv A\pmod 2$; the order $t_{C_D}(A)$ is finite, is at least $|A|$, and equals $|A|$ exactly when the joint cumulant $\kappa_C(A)$ of the spins $((-1)^{U_e})_{e\in A}$, $U\sim\mathrm{Unif}(C)$, is nonzero;
--   2. for any $w\ge1$ and any two offset sequences $\ell,\ell'$ of width $w$ with distinct profiles $T_C(\ell)\ne T_C(\ell')$,
--   $$
--   s(\ell,\ell')=\min_{\substack{D\text{ informative},\ 0\ne A\in C_D^\perp\\ n_A(\ell)\ne n_A(\ell')}} t_{C_D}(A).
--   $$
--
--   For an informative indecomposable code the only block is the whole coordinate set and item 2 is the paper's identity (5); for a general code the minimum is over characters supported on a single informative block, with the order defined on that block. The first changed moment degree is thus read off from the code invariants $t_{C_D}(A)$ of the characters whose counts change.
--
--   Differences from the source:
--   - generalization: item 1 for an informative indecomposable block → item 1 for every informative block $D$ of a code without identically zero coordinates; reason: the block quantities $C_D^\perp$, $L_A$, $t_{C_D}(A)$ and $\kappa$ are those of the block code $C_D$, and an informative indecomposable code is the case of its single block.
--   - encoding: $L_A=q^{-1}\sum_{\sigma\in Q_D}$ → $2^{-m}\sum_{x\in\mathbb F_2^m}$; reason: each block coset has $2^m/q$ representatives and the summand depends only on the coset.
--   - encoding: $\kappa_C(A)$ under $U\sim\mathrm{Unif}(C_D)$ → under $U\sim\mathrm{Unif}(C)$; reason: the marginal of $\mathrm{Unif}(C)$ on a block $D\supseteq A$ is $\mathrm{Unif}(C_D)$.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 3 and eq. (5), printed p. 4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Orders

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-- Theorem 3 (Character formula), printed p. 4 (PDF p. 5), for a code `C` without identically
zero coordinates, stated on every informative block `D` (an informative indecomposable code is
the case of its single block `D = univ`):
1. every monomial `z^v` of `L_A` has `v ≡ A (mod 2)`; `t_{C_D}(A)` is finite, at least `|A|`,
   and equals `|A|` exactly when the joint spin cumulant `κ_C(A)` is nonzero;
2. for distinct equal-width profiles, `s(ℓ, ℓ′)` is the minimum of `t_{C_D}(A)` over the
   characters `A ≠ 0` supported on a single informative block `D` with `n_A(ℓ) ≠ n_A(ℓ′)`. -/
theorem theorem_3 {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (hC : HasNoZeroCoord C) :
    (∀ D ∈ informativeBlocks C, ∀ A ∈ blockDual C D, A ≠ 0 →
      (∀ v : Fin m →₀ ℕ, MvPowerSeries.coeff v (logChar C D A) ≠ 0 →
        ∀ e : Fin m, ((v e : ℕ) : ZMod 2) = A e) ∧
      detOrder C D A ≠ ⊤ ∧
      (weight A : ℕ∞) ≤ detOrder C D A ∧
      (detOrder C D A = (weight A : ℕ∞) ↔ spinCumulant C A ≠ 0)) ∧
    (∀ w : ℕ, 0 < w → ∀ ℓ ℓ' : Fin w → Word m, profile C ℓ ≠ profile C ℓ' →
      momentOrder C ℓ ℓ' =
        ⨅ D ∈ informativeBlocks C, ⨅ A ∈ blockDual C D,
          ⨅ (_ : A ≠ 0 ∧ charCount A ℓ ≠ charCount A ℓ'), detOrder C D A) := by sorry

end AggregatedCodeTesting.Testing
