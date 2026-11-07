-- Prove2me | Theorems.Thm_DSICHardRev_lemma_3_8
-- name    : DSICHardRev.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:41.149503+00:00
-- url     : https://prove2.me/theorems/c37abb44-310e-46c4-b4c7-3a918114b55c
-- title:
--   Lemma 3.8 — short messages leave $j_{k,\vartheta}$ nearly uniform
-- statement:
--   Let $\lambda,\eta\ge1$ and let $N$ be a set of $\eta$ bidders. Let $j=(j_\ell)_{\ell\in[\lambda]}$ be uniform on $N^{[\lambda]}$, let $\Phi$ be a random variable with finite range, and let $\vartheta$ be uniform on $[\lambda]$, with $j,\Phi,\vartheta$ independent. Let $\mu=f(j,\Phi)$ take fewer than $2^{\lambda/\eta^2}$ values. Then
--   $$\mathbb E\Big[\mathrm{TV}\big(\mathrm{Law}(j_\vartheta\mid\mu,\Phi,\vartheta),\,\mathrm{Unif}(N)\big)\Big]\;\le\;\frac1\eta,$$
--   the expectation being over $(\mu,\Phi,\vartheta)$.
--
--   In the paper $N=N_k$, $j=j_k$, $\Phi=\varphi_k$ and $\mu=\mu_k(j_k)$ is the concatenation of the messages of group $N_k$ under a deterministic simultaneous algorithm with fewer than $\lambda/\eta^2$ bits of communication; the lemma says the referee can hardly tell which member of $N_k$ values $A_k$.
--
--   Differences from the source:
--   - generalization: j_k, φ_k, ϑ of a KSSHD and the concatenated messages µ_k(j_k) of group N_k of a deterministic simultaneous algorithm using less than λ/η² communication → j uniform on N^[λ], any finite-range Φ, ϑ uniform, mutually independent, and any µ = f(j, Φ) with fewer than 2^{λ/η²} values; reason: in a KSSHD j_k is uniform and independent of (φ_k, ϑ), φ_k is independent of ϑ (its marginal is a uniform injection for every ϑ), and µ_k is a function of (j_k, φ_k) with fewer than 2^{λ/η²} values, so the paper's case is an instance
--   - reading: discrete random variables → random variables with finite ranges on a finite probability space; reason: Definition 2.22's bound log|X| presupposes finite ranges and every variable the paper uses is finite; the quantities depend only on the joint law
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §3.2, p.15, Lemma 3.8 (inside the proof of Theorem 3.7)

import Mathlib
import Definitions.Def_DSICHardRev_Information

namespace DSICHardRev

/-- **Lemma 3.8** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §3.2, p.15):
for all `k ∈ [κ]`, `E[TV(Law(j_{k,ϑ} | µ_k(j_k), φ_k, ϑ), Unif(N_k))] ≤ η^{-1}`.

**Formalization Note.** Stated self-contained, for the situation of the proof of Theorem 3.7: the
group `N_k` is `Fin η` (`η ≥ 1`), `j = j_k` is uniform on `N_k^{[λ]}` (`λ ≥ 1`, Property (6)), `Φ`
(standing for `φ_k`) has an arbitrary law `pΦ` on a finite type, `ϑ` is uniform on `[λ]`, and
`j, Φ, ϑ` are independent: the joint law `P` has weight `pΦ(φ) / (η^λ λ)` at `(j, φ, ϑ)`. The
messages `µ = f(j, Φ)` take fewer than `2^{λ/η²}` values. The expectation is over `(µ, Φ, ϑ)`. -/
theorem lemma_3_8 (lam η : ℕ) (hlam : 0 < lam) (hη : 0 < η) {Φ Msg : Type} [Fintype Φ]
    [Fintype Msg] (pΦ : Φ → ℝ) (f : (Fin lam → Fin η) → Φ → Msg)
    (hMsg : (Fintype.card Msg : ℝ) < (2 : ℝ) ^ ((lam : ℝ) / (η : ℝ) ^ 2))
    (P : FinProb ((Fin lam → Fin η) × Φ × Fin lam))
    (hP : ∀ j φ θ, P.p (j, φ, θ) = pΦ φ / ((η : ℝ) ^ lam * lam)) :
    P.expectOver (fun ω => (f ω.1 ω.2.1, ω.2.1, ω.2.2))
        (fun y => tv (P.condLaw (fun ω => ω.1 ω.2.2) (fun ω => (f ω.1 ω.2.1, ω.2.1, ω.2.2)) y)
          (fun _ => 1 / (η : ℝ))) ≤ 1 / (η : ℝ) := by sorry

end DSICHardRev
