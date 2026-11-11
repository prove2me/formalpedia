-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_16
-- name    : DPCutRelease.Main.lemma_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:27.535125+00:00
-- url     : https://prove2.me/theorems/26eed027-260f-4214-b088-1f15494a2cf3
-- title:
--   Lemma 16 — success-charged composition: ε = 4L + 4ℓ* log(1/δ″), δ = δ″ + (1 + e^ε)kδ′
-- statement:
--   Let $M_1,\dots,M_k$ be adaptively chosen mechanisms whose outputs are either a valid result in $Y$ or a failure symbol $\bot$ (kernels $\kappa_w^{(t)}$ on transcript prefixes). Fix $\ell^*<1/10$, $\delta'\ge0$ and $L$. Suppose that for every pair of adjacent inputs $w,w'$ — writing $P^0_t,P^1_t$ for the conditional output laws of $M_t(w),M_t(w')$ at a common prefix $y_{<t}$ — there are auxiliary probability kernels $N^0_t,N^1_t$ and losses $0\le\ell_t(y_{<t})\le\ell^*$ such that for every step $t$, every prefix, every measurable $A$ and $b\in\{0,1\}$:
--   - if $P^b_t(A)=0$ then $N^b_t(A)=0$;
--   - $|P^b_t(A)-N^b_t(A)|\le\delta'$;
--   - $e^{-\ell_t}N^1_t(A)\le N^0_t(A)\le e^{\ell_t}N^1_t(A)$;
--
--   and for $b\in\{0,1\}$, almost surely along the auxiliary process $y_t\sim N^b_t(\cdot\mid y_{<t})$,
--   $$\sum_{t=1}^k\ell_t(y_{<t})\,\mathbf 1[y_t\ne\bot]\le L .$$
--   Then for every $\delta''\in(0,1)$ the adaptive composition $(M_1,\dots,M_k)$ is $(\varepsilon,\delta)$ edge-DP with
--   $$\varepsilon=4L+4\ell^*\log(1/\delta''),\qquad\delta=\delta''+(1+e^{\varepsilon})k\delta'.$$
--   It charges privacy only to successful attempts, which is what makes the $O(n^2)$ calls of Algorithm 3 affordable (Lemma 17).
--
--   **Formalization Note.** Outputs are `Option Y` (`none` $=\bot$, an atom of the σ-algebra); $N^b$, $\ell$ may depend on the adjacent pair and on the prefix, while $\ell^*,\delta',L$ are fixed before the pair.
--
--   Differences from the source:
--   - reading: "auxiliary probability measures N⁰ₜ and N¹ₜ" for every prefix, with outputs "sampled sequentially according to yₜ ∼ Nᵇₜ(· | y<t)" → Markov kernels N0 i, N1 i from prefixes; reason: sequential sampling from the auxiliary laws presupposes that they form kernels
--   - reading: "for any sequence of outputs y₁, …, y_k sampled sequentially according to yₜ ∼ Nᵇₜ, Σ ℓₜ 1[yₜ ≠ ⊥] ≤ L" → ∀ᵐ y ∂ transcriptLaw Nᵇ k, Σ ≤ L, for b = 0, 1; reason: a bound on sampled sequences is a bound almost surely along the auxiliary process
--   - reading: ℓ*, δ′ "global constants", L "a deterministic bound"; ℓₜ "may depend on the fixed input pair and the common history" → ℓ*, δ′, L fixed before the adjacent pair; N⁰, N¹, ℓ chosen per pair; reason: ε and δ of the conclusion must not depend on the pair; the note after the lemma allows ℓₜ to
--   - encoding: failure symbol ⊥ → none : Option Y, with A measurable iff its trace on Y is; reason: ⊥ is an extra atom
--   - encoding: Pr[M(w) ∈ A] ≤ e^ε Pr[M(w′) ∈ A] + δ for adjacent w, w′ and measurable A, and symmetrically → IsEdgeDP / IsEdgeDPFun: the inequality between real numbers (toReal) for every ordered adjacent pair; reason: adjacency is symmetric, so the swapped clause is the same condition; every law involved is a probability measure
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 23, Lemma 16 (proof in Appendix A, p. 40)

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_Adaptive

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 16 (Success-Charged Composition, p. 23): mechanisms with outputs in `Option Y`
(`none` = the failure symbol `⊥`). If for every adjacent pair there are auxiliary Markov kernels
`N⁰, N¹` and losses `0 ≤ ℓ_t(y<t) ≤ ℓ* < 1/10` with the three conditions at every step `t < k` and
every common prefix, and the success-charged loss `Σ_t ℓ_t(y<t) 1[y_t ≠ ⊥]` is at most `L` almost
surely along both auxiliary processes, then for every `δ'' ∈ (0, 1)` the composition is `(ε, δ)`
edge-DP with `ε = 4L + 4ℓ* log(1/δ'')`, `δ = δ'' + (1 + e^ε) k δ'`. -/
theorem lemma_16 {n : ℕ} {Y : Type*} [MeasurableSpace Y] (k : ℕ)
    (κ : EdgeVec n → (i : ℕ) → Kernel (Fin i → Option Y) (Option Y))
    [∀ w i, IsMarkovKernel (κ w i)] (ellStar δ' L δ'' : ℝ)
    (hell : ellStar < 1 / 10) (hδ' : 0 ≤ δ') (hδ''0 : 0 < δ'') (hδ''1 : δ'' < 1)
    (hcond : ∀ w w' : EdgeVec n, Adjacent w w' →
      ∃ (N0 N1 : (i : ℕ) → Kernel (Fin i → Option Y) (Option Y))
        (ell : (i : ℕ) → (Fin i → Option Y) → ℝ),
        (∀ i, IsMarkovKernel (N0 i)) ∧ (∀ i, IsMarkovKernel (N1 i)) ∧
        (∀ i < k, ∀ y : Fin i → Option Y, 0 ≤ ell i y ∧ ell i y ≤ ellStar) ∧
        (∀ i < k, ∀ y : Fin i → Option Y, ∀ A : Set (Option Y), MeasurableSet A →
          (κ w i y A = 0 → N0 i y A = 0) ∧ (κ w' i y A = 0 → N1 i y A = 0) ∧
          |(κ w i y A).toReal - (N0 i y A).toReal| ≤ δ' ∧
          |(κ w' i y A).toReal - (N1 i y A).toReal| ≤ δ' ∧
          ENNReal.ofReal (Real.exp (-ell i y)) * N1 i y A ≤ N0 i y A ∧
          N0 i y A ≤ ENNReal.ofReal (Real.exp (ell i y)) * N1 i y A) ∧
        (∀ᵐ y ∂(transcriptLaw N0 k),
          ∑ t : Fin k, ell t.val (prefixOf y t) * (if y t = none then 0 else 1) ≤ L) ∧
        (∀ᵐ y ∂(transcriptLaw N1 k),
          ∑ t : Fin k, ell t.val (prefixOf y t) * (if y t = none then 0 else 1) ≤ L)) :
    IsEdgeDP (fun w => transcriptLaw (κ w) k) (4 * L + 4 * ellStar * Real.log (1 / δ''))
      (δ'' + (1 + Real.exp (4 * L + 4 * ellStar * Real.log (1 / δ''))) * k * δ') := by sorry

end DPCutRelease.Main
