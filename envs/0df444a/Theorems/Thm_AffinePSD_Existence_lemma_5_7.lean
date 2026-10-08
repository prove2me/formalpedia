-- Prove2me | Theorems.Thm_AffinePSD_Existence_lemma_5_7
-- name    : AffinePSD.Existence.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:38.660987+00:00
-- url     : https://prove2.me/theorems/823e590b-c573-4649-9cd1-6019ca2b6151
-- title:
--   Lemma 5.7 (second part) — ⟨b − ½ Σ Dσ^{kl}_{ε,n}(x) σ^{kl}_{ε,n}(x), u⟩ ≥ 0 on the boundary if b ⪰ (d−1)Σ^⊤Σ
-- statement:
--   Let $\varepsilon>0$, $n\in\mathbb N$, $\phi_n,\eta_\varepsilon$ be cut-offs as in (5.4) and §5.2, $\Sigma,b\in M_d$, and let $\sigma^{kl}_{\varepsilon,n}$ be given by (5.8). If
--   $$b\succeq(d-1)\Sigma^\top\Sigma,\tag{5.16}$$
--   then
--   $$\Big\langle b-\frac12\sum_{k,l=1}^dD\sigma^{kl}_{\varepsilon,n}(x)\,\sigma^{kl}_{\varepsilon,n}(x),\,u\Big\rangle\ge0\tag{5.17}$$
--   for all $x\in\partial S_d^+$ and all $u\in N_{S_d^+}(x)=\{u\in S_d^+:\langle u,x\rangle=0\}$.
--
--   This is the boundary condition that keeps the regularized diffusion inside $S_d^+$ (Lemma 5.6). The condition $b\succeq(d-1)\alpha$ of Definition 2.3 is exactly (5.16) with $\alpha=\Sigma^\top\Sigma$.
--
--   **Formalization Note** $D\sigma(x)\sigma(x)$ is the Fréchet derivative of $\sigma^{kl}_{\varepsilon,n}$ at $x$ in the symmetric direction $\sigma^{kl}_{\varepsilon,n}(x)$; the map factors through $x\mapsto(x+x^\top)/2$, so this is the derivative along $S_d$. $b$ and $\Sigma$ are arbitrary, since the lemma uses no other parameter. The lemma's first part, the explicit spectral formula (5.15), is not stated here.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 5.7, (5.16)–(5.17), pp. 45–46; (2.23), p. 12

import Mathlib
import Definitions.Def_AffinePSD_Existence_Cone
import Definitions.Def_AffinePSD_Existence_Regularization

namespace AffinePSD.Existence

/-- Lemma 5.7, "Furthermore" part (arXiv:0910.0137v3, §5.2, p. 46): with `σ^{kl}_{ε,n}` defined by
(5.8) from a matrix `Σ`, if `b ⪰ (d − 1)Σ^⊤Σ` (5.16), then
`⟨b − ½ Σ_{k,l} Dσ^{kl}_{ε,n}(x) σ^{kl}_{ε,n}(x), u⟩ ≥ 0` (5.17) for all `x ∈ ∂S_d^+` and all
`u ∈ N_{S_d^+}(x) = {u ∈ S_d^+ | ⟨u, x⟩ = 0}` (2.23).
Formalization Note: `ϕ_n`, `η_ε` are any cut-offs with the properties (5.4) and p. 42, `ε > 0`,
`n ∈ ℕ`; `b` and `Σ` are arbitrary matrices (the lemma uses no other parameter);
`Dσ(x)σ(x)` is the Fréchet derivative of `σ^{kl}_{ε,n}` (a map on `M_d` that factors through
`x ↦ (x + x^⊤)/2`) at `x` in the symmetric direction `σ^{kl}_{ε,n}(x)`; `∂S_d^+` is
`S_d^+ \ S_d^{++}`. The explicit formula (5.15) of the lemma's first part is not stated. -/
theorem lemma_5_7 {d : ℕ} (n : ℕ) (ε : ℝ) (hε : 0 < ε) (ϕ η : Mat d → ℝ)
    (hϕ : IsPhiN n ϕ) (hη : IsEtaEps ε η) (Sg b : Mat d)
    (hb : PSD (b - ((d : ℝ) - 1) • mmul (transpose Sg) Sg)) :
    ∀ x, PSD x → ¬ PD x → ∀ u, PSD u → tr u x = 0 →
      0 ≤ tr (b - (1 / 2 : ℝ) • ∑ k, ∑ l,
        fderiv ℝ (sigmaReg ϕ η ε Sg k l) x (sigmaReg ϕ η ε Sg k l x)) u := by sorry

end AffinePSD.Existence
