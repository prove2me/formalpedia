-- Prove2me | Theorems.Thm_AffinePSD_Existence_lemma_5_5
-- name    : AffinePSD.Existence.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:35.740466+00:00
-- url     : https://prove2.me/theorems/7c0e8baf-4670-4490-96b5-bfd663943b6c
-- title:
--   Lemma 5.5 — S ⊂ D(A^{ε,δ,n}) and A^{ε,δ,n} f → A f uniformly for f ∈ S_+
-- statement:
--   Let $(\alpha,b,\beta^{ij},c=0,\gamma=0,m,\mu)$ be an admissible parameter set, and let $(\phi_n)_n$ and $(\eta_\varepsilon)_{\varepsilon>0}$ be cut-offs as in (5.4) and §5.2. Then:
--   1. for all $\varepsilon,\delta>0$ and $n$, every rapidly decreasing $f$ on $S_d$ is in the domain of $\mathcal A^{\varepsilon,\delta,n}$: the integrals in (5.10) converge, and $\mathcal A^{\varepsilon,\delta,n}f$ is continuous on $S_d$ and vanishes at infinity;
--   2. for every $f\in\mathcal S_+$,
--   $$\lim_{\varepsilon,\delta,n}\big\|\mathcal A^{\varepsilon,\delta,n}f-\mathcal Af\big\|_\infty=0.\tag{5.11}$$
--
--   This is the approximation step: martingale-problem solutions for $\mathcal A^{\varepsilon,\delta,n}$ have a limit that solves the problem for $\mathcal A$.
--
--   **Formalization Note** Rapidly decreasing functions are restrictions of Schwartz functions on $M_d$. The cut-offs are arbitrary families with the stated properties; the paper fixes some, and uses only those properties. The limit in (5.11) is the joint limit $\varepsilon\to0^+$, $\delta\to0^+$, $n\to\infty$ along the product filter, and $\|\cdot\|_\infty$ is the supremum over $S_d^+$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 5.5, (5.11), p. 43

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params
import Definitions.Def_AffinePSD_Existence_Generator
import Definitions.Def_AffinePSD_Existence_Regularization

open MeasureTheory Filter
open scoped Topology SchwartzMap

namespace AffinePSD.Existence

/-- Lemma 5.5 (arXiv:0910.0137v3, §5.2, p. 43): under the standing assumptions of §5.2 (an
admissible parameter set with `c = 0`, `γ = 0`, p. 41), `S ⊂ D(A^{ε,δ,n})` and, for every
`f ∈ S_+`, `lim_{ε,δ,n} ‖A^{ε,δ,n} f − A f‖_∞ = 0` (5.11).
Formalization Note: the cut-offs `ϕ_n` (5.4) and `η_ε` (p. 42) are arbitrary families with the
stated properties (`IsPhiN`, `IsEtaEps`); the paper fixes some and uses only those properties.
`S ⊂ D(A^{ε,δ,n})` (the operator on `C₀(S_d)`) is: for every Schwartz `F` on `M_d` (whose
restrictions to `S_d` are exactly `S(S_d)`), the integrands of (5.10) are integrable
(`RegIntegrable`), and `A^{ε,δ,n} F` is continuous on `S_d` and tends to `0` at infinity in `S_d`.
`lim_{ε,δ,n}` is the joint limit `ε → 0+`, `δ → 0+`, `n → ∞` along the product filter
`𝓝[>] 0 ×ˢ 𝓝[>] 0 ×ˢ atTop` (the page writes only `lim_{ε,δ,n}`); `‖·‖_∞` is the supremum over
`x ∈ S_d^+`, where `A f` is defined; `f ∈ S_+` is the restriction of a Schwartz `F` to `S_d^+`. -/
theorem lemma_5_5 {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (hP : AffinePSD.Necessity.Admissible χ P)
    (hc : P.c = 0) (hγ : P.γ = 0)
    (ϕ : ℕ → Mat d → ℝ) (hϕ : ∀ n, IsPhiN n (ϕ n))
    (η : ℝ → Mat d → ℝ) (hη : ∀ ε, 0 < ε → IsEtaEps ε (η ε)) :
    (∀ (n : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
      RegIntegrable χ P (ϕ n) δ ∧
      ∀ F : 𝓢(Mat d, ℝ),
        ContinuousOn (Areg χ P (ϕ n) (η ε) ε δ F) {x | IsSym x} ∧
        Tendsto (Areg χ P (ϕ n) (η ε) ε δ F) (cocompact (Mat d) ⊓ 𝓟 {x | IsSym x}) (𝓝 0)) ∧
    ∀ F : 𝓢(Mat d, ℝ), ∀ e > 0,
      ∀ᶠ q : ℝ × ℝ × ℕ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ) ×ˢ atTop,
        ∀ x : Cone d, |Areg χ P (ϕ q.2.2) (η q.1) q.1 q.2.1 F x - AffinePSD.Necessity.Asharp χ P F x| ≤ e := by sorry

end AffinePSD.Existence
