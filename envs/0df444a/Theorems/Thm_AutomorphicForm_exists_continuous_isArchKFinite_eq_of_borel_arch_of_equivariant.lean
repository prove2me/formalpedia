-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant
-- name    : AutomorphicForm.exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/bf9f15a7-ba6f-5a10-beeb-4e48574c8116
-- title:
--   Archimedean induced section at (1,ν) with prescribed K_∞-type
-- statement:
--   Let $K$ be a number field and let $\alpha\colon (\mathbb{A}_K)^\times \to \mathbb{R}^\times$ be the character obtained from the distributive Haar character `distribHaarChar` of the adele ring $\mathbb{A}_K$ by composing with $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units. Assume $\alpha$ takes (strictly) positive real values, and fix $s \in \mathbb{C}$, a character $\nu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ with continuous underlying $\mathbb{C}$-valued function, and a continuous function $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfying `IsArchKFinite`, i.e. for every infinite place $w$ the right translates of $f_\infty$ under `archRowIsometrySubgroup K w` satisfy the finiteness condition `RightTranslatesSpanFinite`. Assume further that for all $m,k \in \mathrm{GL}_2(\mathbb{A}_K)$ with $m$ in the adelic Borel subgroup (lower-left adelic entry zero), with trivial finite parts $\mathrm{glFin}(m)=\mathrm{glFin}(k)=1$, and with $\mathrm{IsRowIsometry}$ holding for the component of $\mathrm{glArch}(m)$, resp. $\mathrm{glArch}(k)$, at every infinite place, one has $f_\infty(mk) = \nu(m_{11}^{(2,2)})\, f_\infty(k)$, where $m_{11}^{(2,2)}$ denotes the $(1,1)$-entry unit `borelDiagSnd` of $m$. Then there exists $\Phi\colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ such that: $\Phi(g)$ depends only on $\mathrm{glArch}(g)$; for every $b$ in the adelic Borel subgroup with $\mathrm{glFin}(b)=1$ and every $g$, $\Phi(bg) = \alpha(b_{00})^{s+1/2}\,\nu(b_{11})\,\alpha(b_{11})^{-(s+1/2)}\,\Phi(g)$, these factors being `etaFst 1 α hα s` and `etaSnd ν α hα s` evaluated at the diagonal units of $b$; $\Phi$ is continuous and satisfies `IsArchKFinite`; and $\Phi(k) = f_\infty(k)$ whenever $\mathrm{glFin}(k)=1$ and every archimedean component of $k$ is row-isometric.
--
--   This is the archimedean half of the construction, by Iwasawa decomposition, of a section in the adelic principal series induced from the pair of characters $(\,\lVert\cdot\rVert^{s+1/2},\ \nu\lVert\cdot\rVert^{-(s+1/2)}\,)$ with a prescribed $K_\infty$-type: the datum on the archimedean maximal compact subgroup is extended to a globally defined, continuous, $K_\infty$-finite function transforming correctly under the Borel subgroup. It is used by [`AutomorphicForm.exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant`](thm.html#AutomorphicForm.exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant), where it is combined with the corresponding datum at the finite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm
open AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (finf : AdelicGL2 (𝓞 K) K → ℂ) (_hfc : Continuous finf) (_hfK : IsArchKFinite K finf)
      (_hfeq : ∀ (m k : AdelicGL2 (𝓞 K) K) (hm : m ∈ adelicBorel (𝓞 K) K),
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          finf (m * k) = ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * finf k),
    ∃ Φ : AdelicGL2 (𝓞 K) K → ℂ,
      (∀ g g' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = glArch (𝓞 K) K g' → Φ g = Φ g') ∧
      (∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K b = 1 →
          Φ (b * g) =
            ((etaFst 1 α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
              ((etaSnd ν α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * Φ g) ∧
      Continuous Φ ∧ IsArchKFinite K Φ ∧
      (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          Φ k = finf k) := by sorry
