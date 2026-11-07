-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_3_4
-- name    : AvgValueAlloc.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:41:55.652047+00:00
-- url     : https://prove2.me/theorems/13e24f39-3965-41df-9b64-f025622b5f9e
-- title:
--   Lemma 3.4 — Local marginal validation
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $M$ fixed ordered funding items with ambiguity at most $\sigma$, $p=\psi(\log(2+\sigma))$ and a shift $s\in\{0,1\}$. Let the funding routing be drawn by the local smoothed rule (ideal softmax) with information records $Y$, and $B_g$ its bank.
--
--   1. For a union of $N$ records split by independent fair bits into $Y$ and $Z$:
--   $$
--   \mathbb E\,G^s_Y(B_g)\le(1+5p)\,\mathbb E\,G^s_Z(B_g).
--   $$
--   2. For every information list $Y$:
--   $$
--   H^s_L(M,Y)\le3\,\mathbb E\bigl[W+G^s_Y(B_g)\bigr]+8p\,P(M),
--   $$
--   where $H^s_L$ maximizes over retained local funding routes.
--
--   Smoothed funding has bounded one-sided influence of each record, which is what lets validation transfer bank marginals in the local branch.
--
--   Differences from the source:
--   - generalization: p = ψ(log(2 + σ_Q)) → p = ψ(log(2 + σ)) for every σ ≥ σ_M; reason: M is part of the live multiset Q, so σ_Q is one such σ; the proof uses only |J(v)| ≤ σ for retained v
--   - generalization: H^s_L(M, Y) ≤ 3E[W + G^s_Y(B_g)] + 8pP(M) for the random information list → for every fixed information list Y; reason: averaging over Y gives the page's form
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3.3, Lemma 3.4, p.9

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_sigmaOn
import Definitions.Def_AvgValueAlloc_Phi
import Definitions.Def_AvgValueAlloc_posVal
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_groupSum
import Definitions.Def_AvgValueAlloc_restrictTo
import Definitions.Def_AvgValueAlloc_pathProb
import Definitions.Def_AvgValueAlloc_HsL
import Definitions.Def_AvgValueAlloc_softmaxKernel

namespace AvgValueAlloc

/-- **Lemma 3.4 (Local marginal validation).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3.3, Lemma 3.4, p.9: "For p = ψ(log(2+σ_Q)), local routing
satisfies EG^s_Y(B_g) ≤ (1+5p)EG^s_Z(B_g), and H^s_L(M, Y) ≤ 3E[W +G^s_Y(B_g)]+8pP(M). Here H^s_L
maximizes over retained local funding routes." Setting, pp.8–9: membership bits of the
information/service union independent and fair; the local smoothed rule.

Let `ρ > 0`, `M` fixed ordered funding items, `σ ≥ σ_M`, `p = ψ(log(2 + σ))` and a shift
`s ∈ {0,1}`. Let the funding routing be drawn by the local softmax rule with information records
`Y`, and `B_g` its bank.
1. For a union `U` of `N` records split by independent fair bits into `Y` and `Z`:
   `E G^s_Y(B_g) ≤ (1 + 5p) E G^s_Z(B_g)` (expectation over the bits and the rule's coins).
2. For every information list `Y`: `H^s_L(M, Y) ≤ 3 E[W + G^s_Y(B_g)] + 8p P(M)`.

**Formalization Note.** `σ` is any upper bound on the ambiguity of `M` (the page's `σ_Q`, as the
live multiset contains `M`); the proof uses it only through `|J(v)| ≤ σ` for retained `v`.
The rule is the ideal (exact) softmax. -/
theorem lemma_3_4 {n m : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (M : Fin m → Vec n) (σ : ℕ)
    (hσ : sigmaOn ρ (Finset.univ.image M) ≤ σ) (s : ℕ) (hs : s ≤ 1) :
    (∀ (N : ℕ) (U : Fin N → Vec n),
      (∑ mb : Fin N → Bool, ∑ X : Fin m → Option (Fin n),
          pathProb (softmaxKernel ρ s (restrictTo U (Finset.univ.filter fun i => mb i = true)) M)
              X *
            Gsh ρ s (restrictTo U (Finset.univ.filter fun i => mb i = true)) (routBank ρ M X)) /
          (2 : ℝ) ^ N ≤
        (1 + 5 * psi (Real.log (2 + (σ : ℝ)))) *
          ((∑ mb : Fin N → Bool, ∑ X : Fin m → Option (Fin n),
            pathProb (softmaxKernel ρ s (restrictTo U (Finset.univ.filter fun i => mb i = true))
                M) X *
              Gsh ρ s (restrictTo U (Finset.univ.filter fun i => mb i = false))
                (routBank ρ M X)) / (2 : ℝ) ^ N)) ∧
    (∀ (ι : Type) [Fintype ι] (Y : ι → Vec n),
      HsL ρ s M Y ≤
        3 * ∑ X : Fin m → Option (Fin n), pathProb (softmaxKernel ρ s Y M) X *
            (welfare M X + Gsh ρ s Y (routBank ρ M X)) +
          8 * psi (Real.log (2 + (σ : ℝ))) * posValSum ρ M) := by sorry

end AvgValueAlloc
