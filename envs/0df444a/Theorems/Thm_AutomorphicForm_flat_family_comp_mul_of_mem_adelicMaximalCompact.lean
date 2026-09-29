-- Prove2me | Theorems.Thm_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact
-- name    : AutomorphicForm.flat_family_comp_mul_of_mem_adelicMaximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/2597dd6f-c5fb-5075-ae89-db6328ec0a30
-- title:
--   Right translation by a maximal compact element preserves flat families
-- statement:
--   Let $F$ be a number field and let $\alpha\colon(\mathbb{A}_F)^\times\to\mathbb{R}^\times$ be the character obtained from the module character `distribHaarChar (AdeleRing (𝓞 F) F)` by composing with $\mathbb{R}_{\ge0}\to\mathbb{R}$ and passing to units; assume $\alpha(t)>0$ for all $t$ (hypothesis $h\alpha$). Let $\varphi\colon\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be such that: for every $s$, $\varphi_s$ is an induced section for the pair of characters $\mathbf{1}\cdot\alpha^{s+1/2}$ and $\mathbf{1}\cdot\alpha^{-(s+1/2)}$, i.e. $\varphi_s(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ for all upper-triangular $b$ and all $g$; for every $s$ and every infinite place $w$ the right translates of $\varphi_s$ under `archRowIsometrySubgroup F w` span a finite-dimensional space; for every $s$, $\varphi_s$ is a smooth vector for the finite adelic subgroup; $(s,g)\mapsto\varphi_s(g)$ is jointly continuous; $s\mapsto\varphi_s(g)$ is differentiable for each $g$; and $\varphi$ is flat, i.e. $\varphi_s(k)=\varphi_{s'}(k)$ whenever the finite part of $k$ lies in `finiteIntegralGL2 (𝓞 F) F` and each archimedean component of $k$ has determinant of norm $1$ and acts isometrically on row vectors for the $\ell^2$-norm. Let $k_0$ belong to `adelicMaximalCompact F`, the subgroup cut out by those same two conditions. Then the right translate $h\mapsto\varphi_s(hk_0)$ satisfies all six conditions again: induced section with the same characters for each $s$, archimedean $K$-finiteness, $K_f$-smoothness, joint continuity of $(s,h)\mapsto\varphi_s(hk_0)$, differentiability in $s$, and flatness in the above sense.
--
--   This is the stability of the class of flat, $K_\infty$-finite, $K_f$-smooth holomorphic families of sections of the principal series $\mathrm{Ind}_B^{\mathrm{GL}_2}(\alpha^{s+1/2},\alpha^{-(s+1/2)})$ under right translation by an element of the adelic maximal compact subgroup, using that $Kk_0=K$ and that conjugation by $k_0$ preserves each local factor. It is used in the analysis of the Weyl intertwining integral near $s=1/2$, where the limit statements for such families are reduced to translates of a given family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem AutomorphicForm.flat_family_comp_mul_of_mem_adelicMaximalCompact
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (k₀ : AdelicGL2 (𝓞 F) F) (_hk₀ : k₀ ∈ adelicMaximalCompact F),
    (∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (fun h => φ s (h * k₀))) ∧
    (∀ s, IsArchKFinite F (fun h => φ s (h * k₀))) ∧
    (∀ s, IsKfSmooth F (fun h => φ s (h * k₀))) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 (p.2 * k₀)) ∧
    (∀ g, Differentiable ℂ (fun s => φ s (g * k₀))) ∧
    (∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s (k * k₀) = φ s' (k * k₀)) := by sorry
