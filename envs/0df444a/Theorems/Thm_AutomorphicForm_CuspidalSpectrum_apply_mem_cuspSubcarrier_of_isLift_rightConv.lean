-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv
-- name    : AutomorphicForm.CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/f16d5bb9-a395-5a95-863f-3eac74e0d3ff
-- title:
--   Lifted right convolution preserves the cuspidal subcarrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb R$ and let $\Phi_0$ be a subset of $\mathrm{GL}_2$ of the adeles of $F$ which is a slab fundamental domain in the sense of `IsSlabFundamentalDomain`: $0<\alpha<\beta$, $\Phi_0$ is contained in the slab $\{g:\lVert\det g\rVert\in[\alpha,\beta]\}$, and $\Phi_0$ is a fundamental domain for the range of the map $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb A_F)$ acting on the adelic Haar measure restricted to that slab. Let $\sigma\in\mathbb R$ and let $\xi$ be a homomorphism from the full subgroup of the idele units to $\mathbb C^\times$ with $\lVert\xi(z)\rVert=\lVert z\rVert^{\sigma}$ for all $z$. Let $f:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ be factorizable, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$. Let $T$ be a continuous $\mathbb C$-linear endomorphism of the carrier $L^2$ space of the weighted measure attached to $\Phi_0$ and $\sigma$, and suppose $T$ is a lift of $\varphi\mapsto\mathrm{rightConv}\,\varphi\,f$ in the sense of `IsLift`: right convolution by $f$ preserves the submodule of continuous members (functions left invariant under the global points, transforming by $\xi$ under the centre, with the relevant integrability, and continuous), and $T$ sends the $L^2$ class of such a $\varphi$ to the class of $\mathrm{rightConv}\,\varphi\,f$. Then $T$ maps the cuspidal subcarrier — the topological closure of the image in $L^2$ of those members that are moreover smooth cuspidal — into itself.
--
--   This is the stability of the cuspidal part of the adelic $L^2$ space under smoothing by a factorizable test function, transported to the $L^2$ carrier attached to a slab fundamental domain. It is used in the construction of compact, symmetric smoothing operators on the cuspidal spectrum and in the corresponding Hecke-operator statements, which invoke it to know that the operators produced act on the cuspidal subcarrier.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T)
    (v : Carrier F Φ₀ σ) (hv : v ∈ cuspSubcarrier F hΦ₀ σ ξ) :
    T v ∈ cuspSubcarrier F hΦ₀ σ ξ := by sorry
