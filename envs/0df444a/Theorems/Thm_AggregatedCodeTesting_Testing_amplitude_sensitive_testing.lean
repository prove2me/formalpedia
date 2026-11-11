-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_amplitude_sensitive_testing
-- name    : AggregatedCodeTesting.Testing.amplitude_sensitive_testing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:16.283891+00:00
-- url     : https://prove2.me/theorems/31a846d8-3cc1-46ee-8e59-4f7be300ec2e
-- title:
--   Theorem 10 — amplitude-sensitive testing: $H^2\asymp\min\{1,\mathcal E_w\}$ and $N^*\asymp 1+\mathcal E_w^{-1}$ on dense parity classes
-- statement:
--   Let $C\le\mathbb F_2^m$ be a binary linear code without identically zero coordinates (not necessarily indecomposable). For offset sequences $\ell,\ell'$ of width $w\ge1$ write $P_\ell,P_{\ell'}$ for the laws of one aggregate observation, $H^2$ for the squared Hellinger distance $\frac12\sum_h(\sqrt{P_\ell(h)}-\sqrt{P_{\ell'}(h)})^2$, $N^*(\ell,\ell')$ for the optimal sample count at error $1/4$, and
--
--   $$
--   \mathcal E_w(\ell,\ell')=\sum_{D\text{ informative}}\ \sum_{0\ne A\in C_D^\perp}\frac{\big(\hat n_{D,A}(\ell')-\hat n_{D,A}(\ell)\big)^2}{w^{t_{C_D}(A)}}
--   $$
--
--   for the character energy. Then:
--
--   1. there is $c_C>0$ such that $H^2(P_\ell,P_{\ell'})\ge c_C\,\mathcal E_w(\ell,\ell')$ for every width $w\ge1$ and every pair with distinct profiles;
--   2. there is $K_C>0$ such that for every width $w\ge1$ and every pair with distinct profiles a selected index exists, and for every selected index $\nu$ (a blockwise multi-index with $1\le|\nu|\le s^*(C)$ maximizing $(c_{\ell'}(\nu)-c_\ell(\nu))^2/w^{|\nu|}$) the midpoint empirical-mean test of $\psi_\nu$ with $\lceil K_C(1+\mathcal E_w^{-1})\rceil$ samples has both errors at most $1/4$;
--   3. for every $\alpha>0$ there are positive constants $c_1,c_2,c_3,c_4$ depending only on $C$ and $\alpha$ such that every distinct, parity-equivalent pair of $\alpha$-dense profiles of any width $w\ge1$ — with no bound on the count differences — satisfies
--   $$
--   c_1\min\{1,\mathcal E_w\}\le H^2(P_\ell,P_{\ell'})\le c_2\min\{1,\mathcal E_w\},\qquad c_3\,(1+\mathcal E_w^{-1})\le N^*(\ell,\ell')\le c_4\,(1+\mathcal E_w^{-1}),
--   $$
--   with $N^*(\ell,\ell')$ finite;
--   4. if the observable parities of $\ell$ and $\ell'$ differ, one sample distinguishes the laws: some one-sample test has both errors equal to $0$.
--
--   Every constant is chosen after the code (and $\alpha$) and before the width and the profiles. The theorem shows that the testing cost on a dense parity class is governed by the amplitudes of all changed characters, weighted by their detection orders, not only by the first changed order; a single moment attains the upper bound.
--
--   Differences from the source:
--   - encoding: $O_C(\cdot)$ and $\asymp_{C,\alpha}$ → explicit positive constants depending only on $C$ (respectively $C,\alpha$), chosen before $w$ and the profiles; reason: this is the meaning of the notation with the stated dependence.
--   - reading: "a single selected Krawtchouk moment gives a test" → every maximizer of the squared normalized mean gap over the blockwise indices $1\le|\nu|\le s^*(C)$, with the midpoint threshold test; reason: this is the selection and the decision rule of the paper's proof, and requiring every maximizer covers any tie convention.
--   - reading: "one sample distinguishes the laws" → a one-sample test with both errors $0$; reason: different parity classes have disjoint supports, which is the paper's justification.
--   - encoding: an energy term with $t_{C_D}(A)=\infty$ → the term $0$, and $\mathcal E_w^{-1}=0$ if $\mathcal E_w=0$; reason: Lean conventions on cases that do not occur, since detection orders are finite (Theorem 3) and $\mathcal E_w>0$ for distinct profiles.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 10 and eq. (11)–(12), printed p. 8 (PDF p. 9); proof printed pp. 8–10 (PDF pp. 9–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Orders
import Definitions.Def_AggregatedCodeTesting_Testing_HypothesisTesting
import Definitions.Def_ReplicableDecisions_hellinger

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-- Theorem 10 (Amplitude-sensitive testing), printed p. 8 (PDF p. 9). Fix a binary linear code
`C` without identically zero coordinates.
1. There is `c_C > 0` with `H²(P_ℓ, P_{ℓ′}) ≥ c_C ℰ_w(ℓ, ℓ′)` for every distinct profile pair.
2. There is `K_C > 0` such that, for every distinct pair, a selected blockwise Krawtchouk moment
   (maximizing the squared normalized mean gap; any maximizer) with the midpoint empirical-mean
   test has both errors at most `1/4` using `⌈K_C (1 + ℰ_w⁻¹)⌉` samples.
3. For every `α > 0` there are constants depending only on `C, α` such that all distinct,
   parity-equivalent, `α`-dense pairs (no bound on count differences) satisfy
   `H² ≍ min{1, ℰ_w}` and `N* ≍ 1 + ℰ_w⁻¹`.
4. If the observable parities differ, one sample distinguishes the laws with zero error. -/
theorem amplitude_sensitive_testing {m : ℕ} (C : Submodule (ZMod 2) (Word m))
    (hC : HasNoZeroCoord C) :
    (∃ c : ℝ, 0 < c ∧ ∀ w : ℕ, 0 < w → ∀ ℓ ℓ' : Fin w → Word m,
      profile C ℓ ≠ profile C ℓ' →
      c * energy C ℓ ℓ' ≤ ReplicableDecisions.hellingerSq (law C ℓ) (law C ℓ')) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ w : ℕ, 0 < w → ∀ ℓ ℓ' : Fin w → Word m,
      profile C ℓ ≠ profile C ℓ' →
      (∃ ν : Fin m → ℕ, IsSelectedIndex C ℓ ℓ' ν) ∧
      ∀ ν : Fin m → ℕ, IsSelectedIndex C ℓ ℓ' ν →
        errorFirst (law C ℓ)
            (momentTest C ℓ ℓ' ν ⌈K * (1 + (energy C ℓ ℓ')⁻¹)⌉₊) ≤ 1 / 4 ∧
        errorSecond (law C ℓ')
            (momentTest C ℓ ℓ' ν ⌈K * (1 + (energy C ℓ ℓ')⁻¹)⌉₊) ≤ 1 / 4) ∧
    (∀ α : ℝ, 0 < α → ∃ c₁ c₂ c₃ c₄ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
      ∀ w : ℕ, 0 < w → ∀ ℓ ℓ' : Fin w → Word m,
        profile C ℓ ≠ profile C ℓ' → ParityEquivalent C ℓ ℓ' →
        IsDense C α ℓ → IsDense C α ℓ' →
        c₁ * min 1 (energy C ℓ ℓ') ≤ ReplicableDecisions.hellingerSq (law C ℓ) (law C ℓ') ∧
        ReplicableDecisions.hellingerSq (law C ℓ) (law C ℓ') ≤ c₂ * min 1 (energy C ℓ ℓ') ∧
        ∃ N : ℕ, sampleComplexity (law C ℓ) (law C ℓ') = (N : ℕ∞) ∧
          c₃ * (1 + (energy C ℓ ℓ')⁻¹) ≤ (N : ℝ) ∧
          (N : ℝ) ≤ c₄ * (1 + (energy C ℓ ℓ')⁻¹)) ∧
    (∀ w : ℕ, 0 < w → ∀ ℓ ℓ' : Fin w → Word m, ¬ ParityEquivalent C ℓ ℓ' →
      ∃ T : (Fin 1 → (Fin m → Fin (w + 1))) → ℝ, IsRandomizedTest T ∧
        errorFirst (law C ℓ) T = 0 ∧ errorSecond (law C ℓ') T = 0) := by sorry

end AggregatedCodeTesting.Testing
