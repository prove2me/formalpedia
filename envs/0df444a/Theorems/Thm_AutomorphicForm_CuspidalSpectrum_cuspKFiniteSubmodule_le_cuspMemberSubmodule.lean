-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
-- name    : AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/f4ebaa34-3c43-57d4-9a27-092f3d8ab2c3
-- title:
--   From Siegel-window cusp forms to slab fundamental domain members
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; assume $D$ satisfies `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in D$. Let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$, and let $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_F)$ satisfy `IsSlabFundamentalDomain F α β Φ₀`: $0<\alpha<\beta$, $\Phi_0$ is contained in the determinant-norm slab between $\alpha$ and $\beta$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the adelic $\mathrm{GL}_2$ Haar measure restricted to that slab. Form the pins `productionPinsOf` over $D$ with the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup everything, level subgroups $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, and the additive adelic Haar measure conditioned on `adelicBox F`. Then the $\mathbb{C}$-span of those continuous $\varphi$ all of whose right translates satisfy `IsSmoothCuspAutomorphicFnAt` at these pins with character $\xi$ and which lie in the archimedean-type cut of some `ArchTypeFamily` is contained in `cuspMemberSubmodule F Φ₀ ξ`, the space of continuous $\varphi$ satisfying `IsSmoothCuspAutomorphicFnAt` at the pins `fdPins F Φ₀` with character $\xi$.
--
--   This is the transfer of cuspidal data from a covering Siegel window to a fundamental domain in a determinant-norm slab: it identifies the $K$-finite cuspidal space built over the window as a subspace of the Hilbert-space carrier attached to $\Phi_0$. It is the bridge by which cuspidal constituents enter the spectral carrier, and it is invoked by the results on decomposing members of isotypic cuspidal subspaces into right convolutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ≤ cuspMemberSubmodule F Φ₀ ξ := by sorry
