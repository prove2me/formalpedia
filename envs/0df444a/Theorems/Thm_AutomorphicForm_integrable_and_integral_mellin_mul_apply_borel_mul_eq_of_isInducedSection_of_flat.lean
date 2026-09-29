-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat
-- name    : AutomorphicForm.integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/667481bd-dcde-52bf-a5da-f4713ef0a32d
-- title:
--   Vertical-line integral of a flat induced-section packet
-- statement:
--   Let $K$ be a number field and let $\alpha$ denote the character of $\mathbb{A}_K^{\times}$ obtained from the distributive Haar character of the adele ring of $K$ by composing with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units; assume $\alpha(x)>0$ for all $x$. Let $\mu,\nu:\mathbb{A}_K^{\times}\to\mathbb{C}^{\times}$ be characters and let $\varphi:\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ be a family subject to two hypotheses: for every $s$, $\varphi_s$ satisfies the induced-section law $\varphi_s(bg)=\chi_1(b_{00})\chi_2(b_{11})\varphi_s(g)$ for all $g$ and all $b$ with lower-left entry $0$, where $\chi_1=\mu\cdot\alpha^{\,s+1/2}$ and $\chi_2=\nu\cdot\alpha^{-(s+1/2)}$ and $b_{00},b_{11}$ are the diagonal entries of $b$ viewed as units; and the family is flat, i.e. $\varphi_s(k)=\varphi_0(k)$ for every $s$ and every $k$ in the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ whose finite part lies in the full integral level-zero subgroup and whose component at each infinite place is a row isometry. Let $h:\mathbb{R}\to\mathbb{C}$ be smooth of compact support, put $c(s)=\int_{\mathbb{R}}h(u)e^{su}\,du$, fix $\sigma'\in\mathbb{R}$, a $b$ with vanishing lower-left entry and a $k$ in that compact subgroup, and set $r=\alpha(b_{00})/\alpha(b_{11})$. Then $t\mapsto c(\sigma'+it)\varphi_{\sigma'+it}(bk)$ is integrable on $\mathbb{R}$ and $$\int_{\mathbb{R}}c(\sigma'+it)\,\varphi_{\sigma'+it}(bk)\,dt=2\pi\,\mu(b_{00})\,\nu(b_{11})\,\sqrt{r}\,h(-\log r)\,\varphi_0(k).$$
--
--   This evaluates a vertical-line (inverse Mellin) integral of a Paley–Wiener weight against a flat family of induced sections in Iwasawa coordinates $bk$, the elementary computation underlying the construction of smooth packets of Eisenstein-type sections. It is used in the assembly of slab profiles from Paley–Wiener packets, via [`AutomorphicForm.isSlabProfile_and_forall_eq_sum_integral_of_paleyWiener_packet`](thm.html#AutomorphicForm.isSlabProfile_and_forall_eq_sum_integral_of_paleyWiener_packet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat.lean

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

theorem AutomorphicForm.integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φ s (k : AdelicGL2 (𝓞 K) K) = φ 0 (k : AdelicGL2 (𝓞 K) K))
      (h : ℝ → ℂ) (_hh : ContDiff ℝ (⊤ : ℕ∞) h) (_hhc : HasCompactSupport h)
      (σ' : ℝ) (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K)
      (k : AdelicGL2 (𝓞 K) K) (_hk : k ∈ adelicMaximalCompact K),
    let c : ℂ → ℂ := fun s => ∫ u : ℝ, h u * Complex.exp (s * (u : ℂ))
    let r : ℝ := ((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) /
      ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ)
    Integrable (fun t : ℝ =>
      c ((σ' : ℂ) + (t : ℂ) * Complex.I) * φ ((σ' : ℂ) + (t : ℂ) * Complex.I) (b * k)) ∧
    ∫ t : ℝ, c ((σ' : ℂ) + (t : ℂ) * Complex.I) * φ ((σ' : ℂ) + (t : ℂ) * Complex.I) (b * k) =
      (((2 * Real.pi) : ℝ) : ℂ) *
        (((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
          ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
          ((Real.sqrt r : ℝ) : ℂ) * h (-Real.log r) * φ 0 k) := by sorry
