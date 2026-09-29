-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_apply_le_of_isInducedSection_etaFst_etaSnd_of_flat_of_isUnitaryChar
-- name    : AutomorphicForm.exists_forall_norm_apply_le_of_isInducedSection_etaFst_etaSnd_of_flat_of_isUnitaryChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/f3bb2bc6-c42a-5bce-afcb-43809a51aaab
-- title:
--   Flat induced-section families are bounded on vertical strips
-- statement:
--   Let $K$ be a number field, and let $\alpha$ denote the character $\mathbb{A}_K^\times \to \mathbb{R}^\times$ obtained from the module `distribHaarChar` of the adele ring by composing with the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passing to units. Assume $\alpha$ takes strictly positive values, let $\mu,\nu : \mathbb{A}_K^\times \to \mathbb{C}^\times$ be characters satisfying $\lVert\mu(x)\rVert = \lVert\nu(x)\rVert = 1$ for all $x$ (unitarity), and let $\varphi : \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, written $\varphi_s(g)$, satisfy: (i) for every $s$, and every $b$ in the subgroup of matrices with vanishing lower-left entry and every $g$, $\varphi_s(bg) = \mu(b_{00})\,\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\,\alpha(b_{11})^{-(s+1/2)}\,\varphi_s(g)$, where the powers are the complex `cpow` of the positive reals $\alpha(b_{ii})$; (ii) $(s,g) \mapsto \varphi_s(g)$ is continuous; (iii) flatness: $\varphi_s(k) = \varphi_0(k)$ for every $s$ and every $k$ in `adelicMaximalCompact K`, the subgroup of elements whose finite part lies in the level-zero integral subgroup and whose component at each infinite place $w$ is a row isometry. Then for every $\sigma_0 \in \mathbb{R}$ and every compact $C \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ there is $M \in \mathbb{R}$ with $\lVert\varphi_{\sigma' + it}(g)\rVert \le M$ whenever $|\sigma'| \le \sigma_0$, $t \in \mathbb{R}$ and $g \in C$.
--
--   This is the standard vertical-strip bound for a flat family of induced sections on $\mathrm{GL}_2(\mathbb{A}_K)$: the norm of such a section is insensitive to the imaginary part of the spectral parameter, so local uniform boundedness in $\sigma$ suffices. It feeds the analytic estimates used in the Paley–Wiener/slab-profile step of the adelic Eisenstein construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_apply_le_of_isInducedSection_etaFst_etaSnd_of_flat_of_isUnitaryChar.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
open IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_forall_norm_apply_le_of_isInducedSection_etaFst_etaSnd_of_flat_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2))
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φ s (k : AdelicGL2 (𝓞 K) K) = φ 0 (k : AdelicGL2 (𝓞 K) K)),
    ∀ (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ M : ℝ, ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, ‖φ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ M := by sorry
