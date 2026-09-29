-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
-- name    : AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/51657c1d-5352-56ff-9b66-8f567a173e1e
-- title:
--   Isotypic cusp forms of principal level split under one smoothing operator
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $W=\bigcup_{x\in T}\{gx : g\in \mathfrak S\}$, where $\mathfrak S$ is the centre-cut Siegel set of those $g$ whose finite component lies in `finiteIntegralGL2`, whose archimedean component has local height $\ge c$ and $x$-window square $\le u^2$ at every infinite place, and whose archimedean determinant norm lies in $[d_1,d_2]$ at every infinite place; assume $W$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^\times$ with $\gamma g z\in W$. Let `pins` be the carrier data `productionPinsOf` attached to $W$, the level family $N\mapsto \mathrm{principalLevel}(N)\sqcap\ker(\mathrm{glArch})$, the Hecke generators `heckeGen`, and the box `adelicBox`, and let $\xi$ be a homomorphism from `pins.Z` $=\top$ to $\mathbb{C}^\times$. Let $N\ne\bot$ be an ideal of $\mathcal O_F$, $S$ a finite set of finite places, `tys` an archimedean type family (finitely many representations `tys.rep w i` at each infinite place $w$), and $\Psi$ a Hecke eigensystem over $\mathbb{C}$. Suppose $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ lies in the span of the functions satisfying `IsIsotypicCuspFormAt` for `pins`, $\xi$, $N$, $S$, $\Psi$, and also in $\bigsqcap_w \bigsqcup_i$ `archTypeSubmoduleAt F w (tys.rep w i)`. Then there are a factorizable test function $f$ (a product of an archimedean and a finite-adelic factor), an $n\in\mathbb{N}$, nonzero scalars $\lambda_1,\dots,\lambda_n$ and functions $\psi_1,\dots,\psi_n$ in the same intersection of submodules, with $\psi_i\ast f:g\mapsto\int \psi_i(gx)f(x)\,d\mu(x)$ equal to $\lambda_i\psi_i$ for each $i$, and $\varphi=\sum_i\psi_i$.
--
--   This is the smoothing step at principal congruence level $K(N)$: a single factorizable convolution kernel diagonalises a given isotypic cusp form of fixed level, Hecke eigensystem and archimedean types into finitely many eigenfunctions with nonzero eigenvalues. It feeds the constituent dictionary [`AutomorphicForm.isotypicCuspSubmodule_principal_inf_archCutSubmodule_le_iSup_isCuspConstituent`](thm.html#AutomorphicForm.isotypicCuspSubmodule_principal_inf_archCutSubmodule_le_iSup_isCuspConstituent) and the subsequent growth and smoothness estimates for such forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (_ : IsFactorizableTestFn F f) (n : ℕ) (lam : Fin n → ℂ) (_ : ∀ i, lam i ≠ 0)
      (ψ : Fin n → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, ψ i ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ∧
        rightConv F (ψ i) f = lam i • ψ i) ∧
      φ = ∑ i, ψ i := by sorry
