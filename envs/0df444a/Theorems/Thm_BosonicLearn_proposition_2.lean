-- Prove2me | Theorems.Thm_BosonicLearn_proposition_2
-- name    : BosonicLearn.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:37:48.1352+00:00
-- url     : https://prove2.me/theorems/b6468257-2e59-4243-970d-d458d5c73dda
-- title:
--   Proposition 2 — $\log\mathbb E_Z L_{\Phi_{X_0}(Z)}(x)\ge-C\xi^2\sum_t(n\nu^2+k_t^2/n)$ for every fixed transcript
-- statement:
--   Assume $1/n\le\nu\le1$, let $R_X=r(I+\xi X)$ with $r=\nu/((1-4\xi)(1+\nu))$, and fix $X_0\in G_{\mathrm{good}}$. For a transcript of $N$ outcomes, the $t$-th POVM element is a rank-one $|\phi_t\rangle\langle\phi_t|$ with $\phi_t\ne0$ in the $k_t$-photon sector, and
--
--   $$L_X(x)=\prod_{t=1}^N\frac{\langle\phi_t|\rho_{R_X}|\phi_t\rangle}{\langle\phi_t|\rho_{R_{X_0}}|\phi_t\rangle}.$$
--
--   There are absolute $C>0$ and $\xi_0$ such that for $\xi\le\xi_0$, $b\in(0,0.1]$ and every such transcript
--
--   $$\log\mathop{\mathbb E}_{Z\sim\mathrm{Unif}(B_{\mathrm{op},b}(0))}L_{\Phi_{X_0}(Z)}(x)\ \ge\ -C\xi^2\sum_{t=1}^N\Big(n\nu^2+\frac{k_t^2}{n}\Big).$$
--
--   Combined with Proposition 1 it shows that the posterior does not concentrate unless $N\gtrsim n/(\nu^2\xi^2)$.
--
--   Differences from the source:
--   - generalization: the rank-one POVM elements |ϕ_t⟩ of a transcript of an adaptive scheme → arbitrary nonzero vectors ϕ_t in the k_t-photon sectors, any N; reason: every transcript has this form after the reduction of §5.4 (pp. 34–35); the proof treats each copy's vector separately
--   - reading: Z ∼ Unif(B_{op,b}(0)) with b a small constant → every b ∈ (0, 0.1]; reason: the proof uses only ‖Φ_{X₀}(Z)‖_op ≤ 4 (Lemma 8, b ≤ 0.1)
--   - encoding: log E_Z L ≥ −Cξ² Σ(…) → E_Z L ≥ exp(−Cξ² Σ(…)), the expectation a lower Lebesgue integral; reason: equivalent; avoids log 0
--   - encoding: ξ "sufficiently small", ξ < 1/32, 1/n ≤ ν ≤ 1 (§5.1) → ∃ ξ₀ ∈ (0, 1/32), ∀ ξ ∈ (0, ξ₀], n ≥ 1, ν ∈ [1/n, 1]; reason: the standing assumptions of §5.1
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Proposition 2, Eq. (90), p. 38

import Mathlib
import Definitions.Def_BosonicLearn_PhiMap
import Definitions.Def_BosonicLearn_Ggood
import Definitions.Def_BosonicLearn_herm0Ball
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn

/-- **Proposition 2 (Likelihood ratio bound for a fixed transcript).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Proposition 2, Eq. (90), p. 38: "Fix X_0 ∈ G_good. For any transcript of measurement outcomes x := (z, k)
where k_t denotes the measured photon number of the t-th copy, log E_Z L_{Φ_{X_0}(Z)}(x) ≥ −Cξ² Σ_{t=1}^N (nν² + k_t²/n),
where Z ∼ Unif(B_{op,b}(0)) and C is some positive constant."
Setting (§5.1, §5.4, pp. 30, 34–35): `1/n ≤ ν ≤ 1`, `R_X = r(I + ξX)`, the POVM elements are rank one and
block diagonal, `|ϕ_t⟩ ∈ H_{k_t}^{(n)}`, and `L_X(x) = ∏_t ⟨ϕ_t|ρ_{R_X}|ϕ_t⟩ / ⟨ϕ_t|ρ_{R_{X_0}}|ϕ_t⟩` (Eq. (63)).

There are absolute `C > 0` and `ξ₀ ∈ (0, 1/32)` such that for all `n ≥ 1`, `ν ∈ [1/n, 1]`, `ξ ∈ (0, ξ₀]`, `X₀ ∈ G_good`,
`b ∈ (0, 0.1]`, all `N`, photon numbers `k_1, …, k_N` and nonzero vectors `ϕ_t` in the `k_t`-photon sectors,
$$\mathbb E_{Z∼\mathrm{Unif}(B_{op,b}(0))} \prod_{t} \frac{⟨ϕ_t|ρ_{R_{Φ_{X_0}(Z)}}|ϕ_t⟩}{⟨ϕ_t|ρ_{R_{X_0}}|ϕ_t⟩} \ge \exp\Big(-Cξ^2 \sum_{t=1}^N (nν^2 + k_t^2/n)\Big).$$

**Formalization Note.** The log form is exponentiated (no `log 0` junk), and the expectation is a lower Lebesgue
integral. Stated for arbitrary sector vectors `ϕ_t`, which include the rank-one POVM elements of every transcript of
every adaptive scheme (see the Differences list). -/
theorem proposition_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ X₀ ∈ Ggood n, ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∀ (N : ℕ) (k : Fin N → ℕ) (ϕ : Fin N → Occupation (Fin n) → ℂ),
        (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
        ENNReal.ofReal (Real.exp (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))) ≤
          ∫⁻ Z, ENNReal.ofReal (∏ t,
              (∑' u, ∑' v, star (ϕ t u) *
                fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) u v * ϕ t v).re /
              (∑' u, ∑' v, star (ϕ t u) * fugacityCoeff (fugacityFamily ν ξ X₀) u v * ϕ t v).re)
            ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by sorry

end BosonicLearn
