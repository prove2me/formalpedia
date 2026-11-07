-- Prove2me | Theorems.Thm_CompNonlocal_lemma_9_gap_upper_bound
-- name    : CompNonlocal.lemma_9_gap_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:50.155038+00:00
-- url     : https://prove2.me/theorems/f2263fb0-309e-4ea5-895b-f756273d0459
-- title:
--   Lemma 9, p.31 — computational gap upper bound: $h_u=\mathfrak b+u\mathfrak a$, $\mathfrak a\le\frac12$, $\gamma\le(v-\frac13)\mathfrak a+\mathsf{negl}\le\Gamma_{\mathrm{comp}}(v)+\mathsf{negl}$
-- statement:
--   Fix a one-round single-copy certification game $G=(Q,A,B,\mathrm{Val})$ and let $h_u$ be the honest acceptance probability on the Werner state $\rho(u)$, $u\in[0,1]$. With the baseline $\mathfrak b$ and alignment $\mathfrak a$ of Definition 13:
--
--   1. for every $\kappa$ and every $u\in[0,1]$,
--   $$h_u=\mathfrak b+u\,\mathfrak a,\qquad \mathfrak a\le\tfrac12; \tag{19}$$
--   2. if $G$ witnesses that $\rho(v)$, $v\in(1/3,1]$, is $\gamma$-single-copy certifiable, then there is a negligible $\mu$ with, for every $\kappa$,
--   $$\gamma\le(v-\tfrac13)\,\mathfrak a+\mu(\kappa)\le\Gamma_{\mathrm{comp}}(v)+\mu(\kappa). \tag{20}$$
--
--   The second part shows that no single-copy certificate of $\rho(v)$ has gap above $\Gamma_{\mathrm{comp}}(v)=\frac12(v-\frac13)$, the benchmark against which Theorem 6 measures near-optimality.
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: Val outputs a score w ∈ [0, 1] (Def 8) or v ∈ [−1, 1] ∪ {⊥} (Def 9); acceptance is the event v₁ < 0, a discarded round rejected (Def 11) → Val outputs one accept bit, its first output bit; reason: only the acceptance event is used for k = 1 (Reading 3)
--   - reading: every family of separable states {τ_AB} (Def 10) → every family of separable density matrices on C² ⊗ C², finite convex combinations of products; reason: the registers of the certified state (Reading 4); larger local spaces would strengthen the hypothesis; every two-qubit separable state is a finite convex combination
--   - encoding: expectations over X and a ← p_X, conditional quantities w_{x,a}, ω_{S|x}, r(t) → sums over the question outcomes with the conditioning multiplied out (unnormalized branches), normalized only at outcomes of positive probability; reason: avoids junk values at probability-0 outcomes; the same numbers
--   - encoding: '≤ negl(κ)' for all sufficiently large κ → ∃ µ negligible, ∀ κ, … ≤ µ κ; reason: the quantities are bounded, so finitely many κ can be absorbed into µ; equivalent
--   - generalization: (19) for the fixed one-round single-copy certificate of a Werner state (§6.3 preamble, p.30), with uniform QPT honest players → (19) for every Certificate (any families Qg, A, B, Val, no uniformity or gap hypothesis), every κ and every u ∈ [0, 1]; reason: the identity and 𝔞 ≤ 1/2 use only that the players' and the verifier's measurements are effects summing to I; a certificate for ρ(v) is an instance
--   - encoding: γ(κ) > 1/poly(κ) for all sufficiently large κ (Def 10) → ∃ q ∈ ℕ[X], eventually 1/(q(κ) + 1) < c(κ) − s(κ) (inside IsCertificateFor); reason: the same class of inverse-polynomial bounds, and no division by 0
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 9, p.31, Eqs. (19)–(20)

import Mathlib
import Definitions.Def_CompNonlocal_IsCertificateFor
import Definitions.Def_CompNonlocal_Certificate_baseline
import Definitions.Def_CompNonlocal_Certificate_align
import Definitions.Def_CompNonlocal_werner
import Definitions.Def_CompNonlocal_gammaComp

set_option autoImplicit false

namespace CompNonlocal

/-- **Lemma 9 (Computational gap upper bound).** Głuch, Morimae, *From Computational Nonlocality to
Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), p.31:
"Let h_u be the honest acceptance probability on ρ(u), for u ∈ [0, 1]. Then h_u = 𝔟 + u𝔞, 𝔞 ≤ 1/2.
(19) If the certificate for ρ(v), with v > 1/3, has single-copy gap γ, then
γ ≤ (v − 1/3)𝔞 + negl(κ) ≤ Γcomp(v) + negl(κ). (20)"

**Formalization Note** `h_u = c.acc κ c.A c.B (werner u)`; `𝔟 = c.baseline κ`, `𝔞 = c.align κ`
(Definition 13). (19) is stated for every certificate and every `κ`; (20) for a certificate
witnessing that `ρ(v)` is γ-single-copy certifiable, with one negligible `µ` for both
inequalities, at every `κ`. The Werner parameter is in the paper's range `v ≤ 1`. -/
theorem lemma_9_gap_upper_bound :
    (∀ (c : Certificate) (κ : ℕ) (u : ℝ), 0 ≤ u → u ≤ 1 →
        c.acc κ c.A c.B (werner u) = c.baseline κ + u * c.align κ ∧ c.align κ ≤ 1 / 2) ∧
    (∀ (c : Certificate) (v γ : ℝ), 1 / 3 < v → v ≤ 1 → IsCertificateFor c (werner v) γ →
        ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ : ℕ,
          γ ≤ (v - 1 / 3) * c.align κ + μ κ ∧
            (v - 1 / 3) * c.align κ + μ κ ≤ gammaComp v + μ κ) := by sorry

end CompNonlocal
