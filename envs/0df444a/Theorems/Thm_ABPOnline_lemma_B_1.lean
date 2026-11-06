-- Prove2me | Theorems.Thm_ABPOnline_lemma_B_1
-- name    : ABPOnline.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:50.799205+00:00
-- url     : https://prove2.me/theorems/23690d23-8760-4caf-88b7-8162580839af
-- title:
--   Lemma B.1 — the discrete filtrations agree: $\mathcal H_0\vee\sigma(Z_1,\dots,Z_k)=\mathcal H_0\vee\sigma(B_{t_0},\dots,B_{t_k})$
-- statement:
--   Let $B$ be an $M$-dimensional Brownian motion, $t_k=k/N$, $\Delta B_{k+1}=B_{t_{k+1}}-B_{t_k}$, and let $\mathcal H_0$ be a $\sigma$-field independent of $\Delta B_1,\dots,\Delta B_N$. Suppose that, for each $0\le k<N$, $b_k$ is $\mathcal H_0\vee\sigma(B_{t_0},\dots,B_{t_k})$-measurable with values in $\mathbb R^M$ and $\|b_k\|_2\le c_G/\sqrt N$. Construct $(Z_{k+1},\varepsilon_{k+1})$ from $\Delta B_{k+1}$ by the inverse map in Lemma 2.5, using the drift $b_k$. Then $Z_1,\dots,Z_N$ are independent $N(0,I_M/N)$ vectors, and for every $0\le k\le N$,
--   $$
--   \mathcal H_0\vee\sigma(Z_1,\dots,Z_k)=\mathcal H_0\vee\sigma(B_{t_0},\dots,B_{t_k})
--   $$
--   after completion.
--
--   The Gaussian inputs and the Brownian mesh carry the same information at every discrete time, so the algorithm can be analysed on the Brownian side.
--
--   Differences from the source:
--   - encoding: H₀ a sigma-field independent of ∆B₁, …, ∆B_N → H₀ a sub-σ-algebra independent of σ(∆B₁, …, ∆B_N) jointly; reason: the standard meaning
--   - encoding: "after completion" → equality of the completions by P-null sets (augmentSigma); reason: the standard meaning
--   - encoding: Z_{k+1}, ε_{k+1} with 1-based indices; L⁰(·; ℝ^M) drifts → coupledZ N b B k (0-based k); b k measurable for H₀ ⊔ meshSigma B N k, with the bound at every sample point; reason: the same objects
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma B.1, (82), p.33 (PDF p.34)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianVec
import Definitions.Def_ABPOnline_augmentSigma
import Definitions.Def_ABPOnline_coupledZ

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

/-- **Lemma B.1** (arXiv:2609.02124, printed p.33, PDF p.34). Let `H₀` be a σ-field independent of
`∆B_1, …, ∆B_N`, and suppose that, for each `0 ≤ k < N`,
`b_k ∈ L⁰(H₀ ∨ σ(B_{t_0}, …, B_{t_k}); ℝ^M)` with `‖b_k‖₂ ≤ c_G/√N`. Construct `(Z_{k+1}, ε_{k+1})`
from `∆B_{k+1}` by the inverse map in Lemma 2.5, using the drift `b_k`. Then `Z_1, …, Z_N` are
independent `N(0, I_M/N)` vectors, and for every `0 ≤ k ≤ N`,
`H₀ ∨ σ(Z_1, …, Z_k) = H₀ ∨ σ(B_{t_0}, …, B_{t_k})` (82) after completion.

**Formalization Note** `B` is an `M`-dimensional Brownian motion (`IsBrownianVec`),
`t_k = k/N`, `∆B_{k+1} = B_{t_{k+1}} − B_{t_k}`; `H₀` is a sub-σ-algebra of the ambient one.
`Z_{k+1}` is `coupledZ N b B k` (0-based index `k`), the inverse steering map (10)–(11) applied to
`(b_k, ∆B_{k+1})`. "After completion" is equality of the completions by `P`-null sets
(`augmentSigma`). -/
theorem lemma_B_1 {Ω : Type*} (H₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hH₀ : H₀ ≤ mΩ) {M N : ℕ}
    (B : Fin M → ℝ≥0 → Ω → ℝ) (hB : IsBrownianVec B P)
    (hind : Indep H₀
      (⨆ k ∈ Finset.range N, MeasurableSpace.comap (meshIncr B N k) inferInstance) P)
    (b : ℕ → Ω → Fin M → ℝ) (hb : ∀ k < N, Measurable[H₀ ⊔ meshSigma B N k] (b k))
    (hbn : ∀ k < N, ∀ ω, l2norm (b k ω) ≤ cG / Real.sqrt N) :
    iIndepFun (fun k : Fin N => coupledZ N b B k) P ∧
    (∀ k < N, P.map (coupledZ N b B k) =
      Measure.pi fun _ : Fin M => gaussianReal 0 (N : ℝ≥0)⁻¹) ∧
    ∀ k ≤ N, augmentSigma P (H₀ ⊔ coupledZSigma N b B k) =
      augmentSigma P (H₀ ⊔ meshSigma B N k) := by sorry

end ABPOnline
