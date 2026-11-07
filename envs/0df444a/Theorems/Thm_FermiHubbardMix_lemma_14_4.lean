-- Prove2me | Theorems.Thm_FermiHubbardMix_lemma_14_4
-- name    : FermiHubbardMix.lemma_14_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:55.078127+00:00
-- url     : https://prove2.me/theorems/4fc91d0d-5ea4-474b-81a5-1e981a3ce8c3
-- title:
--   Lemma 14.4 — onsite contraction $\Phi^{(\delta)}_{i,0}(X)=(1-\kappa_\star z_i\delta)X$
-- statement:
--   Fix a site $i$ and the field-resonant construction, and let $z_i=\sum_{\mu\in F_i}e^{-\beta\varepsilon_\mu}$, $\kappa_\star=e^{-1/4}/\sqrt2$. For $\delta\ge0$ let $\Phi^{(\delta)}_{i,0}(X)=X+\delta\sum_{B\in\mathcal B_i}\int\gamma_B(\omega)\mathcal D_{G^{B,\omega}_{i,0}}(X)\,d\omega$ with $G^{B,\omega}_{i,0}$ from (22). Then:
--
--   1. for every even operator $X$ with $\operatorname{tr}_i(X)=0$, $\Phi^{(\delta)}_{i,0}(X)=(1-\kappa_\star z_i\delta)X$ exactly;
--   2. $1\le z_i\le2^m$;
--   3. for every $0\le\delta\le1/(\kappa_\star2^m)$ and every such $X$,
--   $$
--   \|\Phi^{(\delta)}_{i,0}(X)\|_1=(1-\kappa_\star z_i\delta)\|X\|_1\le(1-\kappa_\star\delta)\|X\|_1 .
--   $$
--   This exact contraction at the resonant frequencies is where the onsite energies drop out of the mixing bound.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: P^i_{µν} = ι_{{i}}(|µ⟩⟨ν|) → c†_µ Π^{{i}}_0 (c†_ν)†; reason: equal up to signs s_µ s_ν ∈ {±1}; the diagonal units coincide and every Lindbladian is quadratic in each jump
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - generalization: Section 14 assumes every v_i diagonal in the occupation basis with min ε_µ = 0 (Definition 13.4) → any onsite terms with any onsite eigenbasis F : FRData (even unitaries U_i ∈ 𝔄_{{i}} with U_i v_i U_i† diagonal); jumps U_i† P^i_{µν} U_i; evolution under H; reason: U_i = I and λ = ε recovers the page; for general U this is the paper's conjugation of Remark 13.3, under which every quantity in the statement is invariant
--   - encoding: 0 ≤ δ ≤ 1/(κ⋆2^m) → 0 ≤ δ and κ⋆ 2^m δ ≤ 1; reason: division-free form of the same condition
--   - encoding: β > 0 (Definition 13.4) → hypothesis 0 < β; reason: the standing assumption of the field-resonant construction
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Lemma 14.4, pp.66–67

import Mathlib
import Definitions.Def_FermiHubbardMix_eulerStep
import Definitions.Def_FermiHubbardMix_ptr
import Definitions.Def_FermiHubbardMix_w1
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Lemma 14.4 (Onsite contraction)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), pp.66–67). Fix a site `i` and the field-resonant
construction of Definition 13.4. For `δ ≥ 0` let `Φ^{(δ)}_{i,0}(X) = X + δ ∑_{B ∈ B_i} ∫ γ_B(ω)
D_{G^{B,ω}_{i,0}}(X) dω` with `G^{B,ω}_{i,0}` from eq. (22), and `z_i = ∑_µ e^{-βε_µ}`. Then
(1) for every even `X` with `tr_i(X) = 0`, `Φ^{(δ)}_{i,0}(X) = (1 - κ⋆ z_i δ) X`;
(2) `1 ≤ z_i ≤ 2^m`;
(3) for `0 ≤ δ ≤ 1/(κ⋆ 2^m)` and every such `X`,
`‖Φ^{(δ)}_{i,0}(X)‖₁ = (1 - κ⋆ z_i δ)‖X‖₁ ≤ (1 - κ⋆ δ)‖X‖₁`.

**Formalization Note** `δ ≤ 1/(κ⋆2^m)` is `κ⋆ 2^m δ ≤ 1`. `ε_µ = λ_i(µ) - min λ_i` are the onsite
energies of the onsite eigenbasis (`FRData`). -/
theorem lemma_14_4 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (hH : H.IsLocal ord) (F : FRData ord H) (β : ℝ)
    (hβ : 0 < β) (i : Λ) :
    (∀ δ : ℝ, 0 ≤ δ → ∀ X : Op N, IsEven X → ptr ord {i} X = 0 →
      onsiteStep ord H F β i δ X = ((1 - kappaStar * F.zSite β i * δ : ℝ) : ℂ) • X) ∧
    (1 ≤ F.zSite β i ∧ F.zSite β i ≤ 2 ^ m) ∧
    (∀ δ : ℝ, 0 ≤ δ → kappaStar * 2 ^ m * δ ≤ 1 → ∀ X : Op N, IsEven X → ptr ord {i} X = 0 →
      WildeQIT.traceNorm (onsiteStep ord H F β i δ X) =
          (1 - kappaStar * F.zSite β i * δ) * WildeQIT.traceNorm X ∧
        (1 - kappaStar * F.zSite β i * δ) * WildeQIT.traceNorm X ≤
          (1 - kappaStar * δ) * WildeQIT.traceNorm X) := by sorry

end FermiHubbardMix
