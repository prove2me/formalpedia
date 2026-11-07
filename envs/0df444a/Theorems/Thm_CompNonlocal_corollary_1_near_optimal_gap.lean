-- Prove2me | Theorems.Thm_CompNonlocal_corollary_1_near_optimal_gap
-- name    : CompNonlocal.corollary_1_near_optimal_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:36.262998+00:00
-- url     : https://prove2.me/theorems/92899ed6-a0d5-4c14-b26b-e6ba028f5c8a
-- title:
--   Corollary 1, p.32 — consequences of a near-optimal gap: $\mathfrak a\ge\frac{1-\delta}2-\mathsf{negl}$ and $h_v-\gamma\le h_{1/3}+\frac\delta3$
-- statement:
--   Let $v\in(1/3,1]$ and $\delta\in[0,1]$, and let $G$ witness that $\rho(v)$ is $\gamma$-single-copy certifiable with
--   $$\gamma\ge(1-\delta)\,\Gamma_{\mathrm{comp}}(v).$$
--   Then
--
--   1. there is a negligible $\mu$ with $\mathfrak a\ge\dfrac{1-\delta}2-\mu(\kappa)$ for every $\kappa$;
--   2. for every $\kappa$, $\;h_v-\gamma\le h_{1/3}+\dfrac\delta3$. $\quad$(22)
--
--   The first bound says the test is nearly maximally aligned with Bob's conditional Bloch vector; the second bounds the soundness threshold, which a good receiver-side estimator would beat (Lemma 15).
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: Val outputs a score w ∈ [0, 1] (Def 8) or v ∈ [−1, 1] ∪ {⊥} (Def 9); acceptance is the event v₁ < 0, a discarded round rejected (Def 11) → Val outputs one accept bit, its first output bit; reason: only the acceptance event is used for k = 1 (Reading 3)
--   - reading: every family of separable states {τ_AB} (Def 10) → every family of separable density matrices on C² ⊗ C², finite convex combinations of products; reason: the registers of the certified state (Reading 4); larger local spaces would strengthen the hypothesis; every two-qubit separable state is a finite convex combination
--   - encoding: expectations over X and a ← p_X, conditional quantities w_{x,a}, ω_{S|x}, r(t) → sums over the question outcomes with the conditioning multiplied out (unnormalized branches), normalized only at outcomes of positive probability; reason: avoids junk values at probability-0 outcomes; the same numbers
--   - encoding: '≤ negl(κ)' for all sufficiently large κ → ∃ µ negligible, ∀ κ, … ≤ µ κ; reason: the quantities are bounded, so finitely many κ can be absorbed into µ; equivalent
--   - encoding: γ(κ) > 1/poly(κ) for all sufficiently large κ (Def 10) → ∃ q ∈ ℕ[X], eventually 1/(q(κ) + 1) < c(κ) − s(κ) (inside IsCertificateFor); reason: the same class of inverse-polynomial bounds, and no division by 0
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Corollary 1, p.32, Eq. (22)

import Mathlib
import Definitions.Def_CompNonlocal_IsCertificateFor
import Definitions.Def_CompNonlocal_Certificate_align
import Definitions.Def_CompNonlocal_werner
import Definitions.Def_CompNonlocal_gammaComp

set_option autoImplicit false

namespace CompNonlocal

/-- **Corollary 1 (Consequences of a near-optimal gap).** Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), p.32: "Let v ∈ (1/3, 1] be fixed and δ ∈ [0, 1]. If the gap γ ≥ (1 − δ)Γcomp(v), then
𝔞 ≥ (1 − δ)/2 − negl(κ), h_v − γ ≤ h_{1/3} + δ/3. (22)"

**Formalization Note** "The gap γ" is that of a certificate `c` witnessing γ-single-copy
certifiability of `ρ(v)`. The first bound has one negligible `µ` for all `κ`; the second holds at
every `κ` with no negligible term, `h_u = c.acc κ c.A c.B (werner u)`. -/
theorem corollary_1_near_optimal_gap (c : Certificate) (v γ δ : ℝ) (hv₁ : 1 / 3 < v)
    (hv₂ : v ≤ 1) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hc : IsCertificateFor c (werner v) γ)
    (hγ : (1 - δ) * gammaComp v ≤ γ) :
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ : ℕ, (1 - δ) / 2 - μ κ ≤ c.align κ) ∧
      ∀ κ : ℕ, c.acc κ c.A c.B (werner v) - γ ≤ c.acc κ c.A c.B (werner (1 / 3)) + δ / 3 := by sorry

end CompNonlocal
