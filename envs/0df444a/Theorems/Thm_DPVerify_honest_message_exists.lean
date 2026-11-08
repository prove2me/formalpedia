-- Prove2me | Theorems.Thm_DPVerify_honest_message_exists
-- name    : DPVerify.honest_message_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:26.986302+00:00
-- url     : https://prove2.me/theorems/e1a0e6d5-4e09-4729-8c16-7892abd10555
-- title:
--   Proof of Theorem 4.1, p.12 — an honest message with $U_m(r)\le t\mu(m)$ exists with probability $\ge1-1/t$
-- statement:
--   Let $\mathcal M$ be a finite set, $L\ge|\mathcal M|$ an integer, and $(U_m)_{m\in\mathcal M}$ pairwise independent random variables, each uniform on $\{1/L,2/L,\dots,1\}$. Let $\mu$ be a probability vector on $\mathcal M$ and $t>1$. Then
--
--   $$
--   \Pr\bigl[U_m>t\mu(m)\ \text{for every } m\in\mathcal M\bigr]\;\le\;\frac1t .
--   $$
--
--   In Theorem 4.1's protocol $U_m=U_m(r)$ is the public hash of the message $m$ and $\mu(m)=\mathbb E_{S\sim D^s}p_S(m)$ is the average probability that the original verifier sends $m$. The statement says that the honest prover finds a message with $U_m(r)\le t\mu(m)$ except with probability $1/t$; it is the first failure condition in the completeness proof.
--
--   Differences from the source:
--   - generalization: $L\ge|\mathcal M|$ the smallest such power of two → any integer $L\ge|\mathcal M|$; reason: the argument uses only $L\ge|\mathcal M|$; the power of two is a special case
--   - generalization: the hash values $U_m(r)$, $r\sim\mathcal R$, and $\mu(m)=\mathbb E_Sp_S(m)$ → any pairwise independent family on any probability space with the uniform laws, and any probability vector $\mu$; reason: the hash family and the message law are instances
--   - encoding: such a message exists with probability at least $1-1/t$ → the probability that no $m$ has $U_m\le t\mu(m)$ is at most $1/t$; reason: complementary event
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Proof of Theorem 4.1, p.12 (PDF p.15)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace DPVerify

/-- §4, proof of Theorem 4.1, existence of an honest message (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.12 = PDF p.15): "Such a message
exists with probability at least `1 − 1/t`." Let `U_m`, `m ∈ M`, be pairwise independent random
variables, each uniform on `{1/L, 2/L, …, 1}` with `L ≥ |M|`; let `μ` be a probability vector on
`M` and `t > 1`. Then `Pr[U_m > t μ(m) for every m] ≤ 1/t`.

**Formalization Note** `L` is any integer `≥ |M|` (the page takes the smallest power of two), and
the bound holds for every such family. Uniformity is `Pr[U_m = k/L] = 1/L` for `k = 1, …, L`. -/
theorem honest_message_exists {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : Type} [Fintype M] (L : ℕ) (hL : Fintype.card M ≤ L)
    (U : M → Ω → ℝ) (hU : ∀ m, Measurable (U m))
    (hunif : ∀ m, ∀ k ∈ Finset.Icc 1 L, P (U m ⁻¹' {(k : ℝ) / L}) = (L : ENNReal)⁻¹)
    (hpair : ∀ m m', m ≠ m' → IndepFun (U m) (U m') P)
    (μ : M → ℝ) (hμ0 : ∀ m, 0 ≤ μ m) (hμ1 : ∑ m, μ m = 1) (t : ℝ) (ht : 1 < t) :
    P {ω | ∀ m, t * μ m < U m ω} ≤ ENNReal.ofReal (1 / t) := by sorry

end DPVerify
