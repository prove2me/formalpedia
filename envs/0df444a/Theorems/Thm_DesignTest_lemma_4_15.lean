-- Prove2me | Theorems.Thm_DesignTest_lemma_4_15
-- name    : DesignTest.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:08.558406+00:00
-- url     : https://prove2.me/theorems/ad17b6c9-bd2b-43dc-bd0e-b6612794ff22
-- title:
--   Lemma 4.15 — distinguishing $\mathrm{Unif}([L])$ from every $p_S$ needs $m\ge\min\{M^2/(\lambda^2L),(1-2\delta)M/(\lambda^2\sqrt L)\}$
-- statement:
--   Let $L,M$ be integers with $1\le M\le L$, $\lambda\in(0,1]$ and $\delta\in[0,1/2)$, and for each size-$M$ subset $S\subseteq[L]$ let $p_S=(1-\lambda)\mathrm{Unif}([L])+\lambda\mathrm{Unif}(S)$. Let $f:[L]^m\to[0,1]$ be a test of $m$ independent samples that distinguishes $\mathrm{Unif}([L])$ from $p_S$ for every fixed $S$ with error at most $\delta$:
--   $$\mathbb E_{\mathrm{Unif}([L])^{\otimes m}}[f]\ge1-\delta,\qquad \mathbb E_{p_S^{\otimes m}}[f]\le\delta\quad\text{for every }S,\ |S|=M .$$
--   Then
--   $$m\ge\min\Big\{\frac{M^2}{\lambda^2L},\ \frac{(1-2\delta)M}{\lambda^2\sqrt L}\Big\}.$$
--
--   It is the second-moment (likelihood-ratio) bound behind the inverse-square sample lower bounds for $t=1,2$.
--
--   **Formalization Note** The expectations are finite sums against the product laws $\prod_iL^{-1}$ and $\prod_ip_S(x_i)$.
--
--   Differences from the source:
--   - generalization: any randomized tester using at most m independent samples in every execution → every function f : (Fin m → Fin L) → [0, 1] of m samples; reason: such a tester is simulated from m presampled samples and its conditional acceptance probability is such an f (p.42)
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Lemma 4.15, eq. (69), p.41

import Mathlib
import Definitions.Def_DesignTest_dilutedLaw

set_option autoImplicit false

namespace DesignTest

/-- **Lemma 4.15** (Sample lower bound for diluted subsets). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing
State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Lemma 4.15, eq. (69), p.41.

Let `L, M` be integers with `M ∈ [1, L]`, `λ ∈ (0, 1]`, `δ ∈ [0, 1/2)`, and for each size-`M` subset
`S ⊆ [L]` let `p_S := (1 − λ) Unif([L]) + λ Unif(S)`. If a test `f : [L]^m → [0, 1]` of `m` independent
samples accepts `Unif([L])^{⊗m}` with probability at least `1 − δ` and accepts `p_S^{⊗m}` with probability
at most `δ` for every size-`M` subset `S`, then `m ≥ min{M²/(λ²L), (1 − 2δ)M/(λ²√L)}`.

**Formalization Note.** A randomized tester using at most `m` samples in every execution is represented by
its conditional acceptance probability given `m` presampled indices (unused samples ignored, p.42); the
statement covers every function `f : (Fin m → Fin L) → [0, 1]`. Acceptance probabilities are finite sums
against the product laws. -/
theorem lemma_4_15 (L M : ℕ) (hM1 : 1 ≤ M) (hML : M ≤ L) (lam δ : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (m : ℕ) (f : (Fin m → Fin L) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hunif : 1 - δ ≤ ∑ x : Fin m → Fin L, f x * ∏ _i : Fin m, (1 / (L : ℝ)))
    (hS : ∀ S : Finset (Fin L), S.card = M →
      ∑ x : Fin m → Fin L, f x * ∏ i : Fin m, dilutedLaw L M lam S (x i) ≤ δ) :
    min ((M : ℝ) ^ 2 / (lam ^ 2 * L)) ((1 - 2 * δ) * M / (lam ^ 2 * Real.sqrt L)) ≤ (m : ℝ) := by sorry

end DesignTest
