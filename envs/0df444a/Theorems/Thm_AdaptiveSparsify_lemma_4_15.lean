-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_4_15
-- name    : AdaptiveSparsify.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:28.983219+00:00
-- url     : https://prove2.me/theorems/09575e85-7d8c-4cfc-9189-e716d182a9dc
-- title:
--   Lemma 4.15 — a nearby $\ell_2$-stable sequence exists with high probability
-- statement:
--   Let $(x^{(k)},s^{(k)})$, $k<T$, be found by repeatedly calling Algorithm 1 with $R$ drawn as in Lemma 6.3, where $T\le n^{C_T}$. With high probability, on the runs that stay well-centered with valid inputs, there is a sequence $\hat x^{(k)}$ such that for all $k<T$ and all blocks $i$,
--
--   1. (Nearby) $\|\nabla^2\phi_i(x^{(k)}_i)^{1/2}(x^{(k)}_i-\hat x^{(k)}_i)\|_2\le\alpha/2$;
--   2. ($\ell_2$-Stability) $\|\hat x^{(k+1)}-\hat x^{(k)}\|_{\nabla^2\Phi(x^{(k)})}\le2\alpha$.
--
--   Although $x^{(k)}$ itself is not $\ell_2$-stable under subsampling, this nearby sequence is, and that is why the approximation $\bar x$ changes only $\tilde O(n)$ times.
--
--   Differences from the source:
--   - reading: "a sequence of points found by repeatedly calling short-step" → the run on a table of independent uniform reals, with t_k = (1 − η)^k t₀ and a measurable policy for x̄, s̄, H, τ̃ that sees all earlier randomness; reason: makes the random process one object; the choices of Algorithm 1 are adaptive
--   - reading: the lemma assumes well-centered iterates implicitly → the bad event is restricted to tapes on which the iterates are well-centered and the inputs valid at every k < T; reason: the proof's stopped potential (p.32) gives this form; other tapes do not make the event vacuous
--   - reading: k ∈ [T], with an unspecified length T → k < T (from 0), T ≤ n^{C_T} for every exponent C_T; reason: the proof takes "a union bound over the polynomially many iterations" (p.32)
--   - reading: "sufficiently small" ε, large C_center, C_var and sample constant, C_K absolute → explicit quantifiers: C_K, then ε₀, then ε, then the other constants in the order of the proof, all before the instance; reason: p.17 and §6.4 hide these constants; they may depend on C_K, which is an absolute constant (reading R1)
--   - reading: §4 assumes n large enough for log n > 0 → n ≥ 2; reason: λ = C_center log n / ε² vanishes at n = 1 and α is then undefined
--   - reading: "with high probability" → failure at most n^{−c} for every c > 0, with the sampling constant chosen after c; reason: Lemma 6.3 scales the failure exponent with its constant
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 4.15, p.29

import Mathlib
import Definitions.Def_AdaptiveSparsify_IPM

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 4.15**, p.29.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 4.15, p.29.

"Let (x^{(k)}, s^{(k)}) for k ∈ [T] be a sequence of points found by repeatedly calling short-step (see
Algorithm 1) with R drawn by Lemma 6.3, whose variance bound is used in the proof. With high
probability, there is a sequence of points x̂^{(k)} such that: 1. (Nearby) For all k ∈ [T] and i ∈ [m] it
holds that ‖∇²φ_i(x_i^{(k)})^{1/2}(x_i^{(k)} − x̂_i^{(k)})‖₂ ≤ α/2, and 2. (ℓ₂-Stability) For all k ∈ [T] it
holds that ‖x̂^{(k+1)} − x̂^{(k)}‖_{∇²Φ(x^{(k)})} ≤ 2α."

**Formalization Note.** The run is `ERMInstance.iterate` on a uniform tape, with `t_k = (1 - η)^k t₀` and a
measurable policy that sees all earlier randomness. Steps are indexed from `0`, so `k ∈ [T]` is `k < T`,
and `x̂^{(T)}` is the `(k+1)`-st point of the last stability clause. The bad event is restricted to tapes on
which all `T` iterates are well-centered and all choices valid: the event is not vacuous when other tapes
leave the central path, and the proof's stopped potential (p.32) gives this form. "With high probability" is
failure at most `n^{-c}` for every `c`. `T` is polynomial in `n` ("the polynomially many iterations of the
algorithm", p.32), for every exponent `CT`. -/
theorem lemma_4_15 : ∀ CK : ℕ, 1 ≤ CK → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 80 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ Cc₀ : ℝ, 0 < Cc₀ ∧ ∀ Cc : ℝ, Cc₀ ≤ Cc →
      ∀ c CT : ℝ, 0 < c → 0 < CT → ∃ Cs₀ : ℝ, 0 < Cs₀ ∧ ∀ Cs : ℝ, Cs₀ ≤ Cs →
        ∀ I : ERMInstance, I.IsAdmissible CK → 2 ≤ I.blocks.n →
        ∀ ν : Fin I.blocks.m → ℝ,
          (∀ i, EntropicBarrier.Universal.IsNuSelfConcordantBarrier (I.K i) (I.φ i) (ν i)) →
          (∀ i, ν i ≤ CK) →
        ∀ (T : ℕ) (i₀ : Fin I.blocks.m) (π : I.Policy) (x₀ s₀ : Fin I.blocks.n → ℝ) (t₀ : ℝ),
          (T : ℝ) ≤ (I.blocks.n : ℝ) ^ CT → 0 < t₀ → (∀ k, Measurable (π k)) →
          let p : Params := ⟨CK, ε, Cc⟩
          let n := I.blocks.n
          let α := p.alpha n
          let η := ε * α / (Cc * Real.sqrt (∑ i, ν i))
          let it := ERMInstance.iterate p Cs η t₀ i₀ π x₀ s₀
          uniformTable {ω |
            (∀ k < T,
              I.WellCentered α ε ((1 - η) ^ k * t₀) (it ω k).1 (it ω k).2 ∧
              (π k (ERMInstance.tablePrefix k ω)).Valid p ((1 - η) ^ k * t₀)
                (it ω k).1 (it ω k).2) ∧
            ¬ ∃ xh : ℕ → Fin n → ℝ,
              (∀ k < T, ∀ i,
                eNorm (matSqrt (I.hess (it ω k).1 i) *ᵥ
                  (I.blocks.restrict (it ω k).1 i - I.blocks.restrict (xh k) i)) ≤ α / 2) ∧
              (∀ k < T, wNorm (I.hessΦ (it ω k).1) (xh (k + 1) - xh k) ≤ 2 * α)} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end AdaptiveSparsify
