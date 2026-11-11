-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_lemma_13
-- name    : AggregatedCodeTesting.Testing.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:26.705602+00:00
-- url     : https://prove2.me/theorems/19601594-b29a-465b-97cf-e0b99106e34d
-- title:
--   Lemma 13 — parity lattice expansion with remainder $K_D w^{-m/2-D/4}$
-- statement:
--   Let $C\le\mathbb F_2^m$ be an indecomposable binary linear code without identically zero coordinates, and fix $M$ and an integer $D\ge1$. There is a constant $K_D=K_D(C,M)$ such that for every width $w\ge1$, every $M$-balanced offset sequence $\ell$ of width $w$, and every $h$ in the observable parity class of $\ell$,
--
--   $$
--   \Big|P_\ell(h)-B_\ell(h)\sum_{\substack{r\in\{0,\dots,w\}^m\\|r|<D}}\frac{c_\ell(r)}{\binom{w}{r}}\psi_r(h)\Big|\le K_D\,w^{-m/2-D/4}.
--   $$
--
--   Here $B_\ell$ is the product binomial law $B$ conditioned on the parity class of $\ell$ (the set of $h$ with $\sum_{e\in A}h_e\equiv n_A(\ell)\pmod 2$ for every dual word $A$).
--
--   This is the local expansion behind the matching upper bound: on the common parity lattice, the law is a low-degree Krawtchouk correction of a conditioned binomial law, with an absolute error uniform in $h$ and $w$.
--
--   Differences from the source:
--   - encoding: "for all $w$" → for all $w\ge1$; reason: the model fixes $w\ge1$ and $w^{-m/2-D/4}$ is undefined at $w=0$.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Appendix A, Lemma 13, printed p. 13 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Model

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-- Lemma 13 (parity lattice expansion), printed p. 13 (PDF p. 14): for `C` indecomposable
without identically zero coordinates and every `M` and `D ≥ 1`, there is `K_D = K_D(C, M)` such
that for every width `w ≥ 1`, every `M`-balanced `ℓ` and every `h` in the parity class of `ℓ`,
`|P_ℓ(h) - B_ℓ(h) ∑_{|r| < D} c_ℓ(r)/binom(w, r) ψ_r(h)| ≤ K_D w^{-m/2 - D/4}`. -/
theorem lemma_13 {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (hC : HasNoZeroCoord C)
    (hCi : IsIndecomposable C) (M : ℝ) (D : ℕ) (hD : 1 ≤ D) :
    ∃ K : ℝ, ∀ w : ℕ, 0 < w → ∀ ℓ : Fin w → Word m, IsBalanced C M ℓ →
      ∀ h ∈ parityClass C ℓ,
        |law C ℓ h - condBinom C ℓ h *
            ∑ r ∈ (lowIndices m w).filter (fun r => absIdx r < D),
              moment C ℓ r / (multiBinom w r : ℝ) * (psi w r h : ℝ)| ≤
          K * (w : ℝ) ^ (-(m : ℝ) / 2 - (D : ℝ) / 4) := by sorry

end AggregatedCodeTesting.Testing
