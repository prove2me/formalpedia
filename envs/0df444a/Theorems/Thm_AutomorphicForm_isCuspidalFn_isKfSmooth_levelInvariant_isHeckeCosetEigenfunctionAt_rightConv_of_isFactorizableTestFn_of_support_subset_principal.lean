-- Prove2me | Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset_principal
-- name    : AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/0dffc23a-c8e3-555d-86a6-598e0af97719
-- title:
--   Right convolution preserves cuspidality, smoothness and Hecke eigenvalues
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers and $T$ a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$, and let $W$ be the union over $x\in T$ of the images of the centre-cut Siegel set with parameters $c,u,d_1,d_2$ (those $g$ whose finite component lies in `finiteIntegralGL2`, with $c\le$ `localHeight`, `xWindowSq` $\le u^2$ and `archDetNorm` $\in[d_1,d_2]$ at every infinite place) under right multiplication by $x$; no inequalities among the parameters and no covering property of $W$ are assumed. Let $\Psi$ be a complex Hecke eigensystem for $K$, with level ideal $\Psi.\mathrm{level}\neq\bot$ and eigenvalues $\Psi.a$, and write $U=$ `principalLevel` $(\Psi.\mathrm{level})\sqcap$ `finiteAdelicGL2Subgroup` $K$, the elements of the principal congruence subgroup whose archimedean component is trivial. Let $R$ be a smooth-cusp realisation of $\Psi$ at the production pins formed from the window $W$, the level family $\mathfrak{N}\mapsto$ `principalLevel` $(\mathfrak N)\sqcap$ `finiteAdelicGL2Subgroup` $K$, the Hecke generators `heckeGen` at the finite places and the box `adelicBox` $K$ (so with full central subgroup, the Borel $\sigma$-algebra and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, and the additive adelic Haar measure conditioned on the box on $\mathbb{A}_K$), and assume the underlying function $R.\mathrm{toFun}=\varphi$ is continuous. Let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a factorizable test function, i.e. $f(x)=f_\infty(x_\infty)f_{\mathrm{fin}}(x_f)$ with $f_\infty$ compactly supported and a smooth function of the matrix entries and $f_{\mathrm{fin}}$ locally constant with compact support, and assume every $x$ with $f(x)\neq 0$ can be written $x=ak$ with $\mathrm{glFin}(a)=1$ and $k\in U$. Then the right convolution $\varphi\ast f:g\mapsto\int \varphi(gx)f(x)$ against adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfies: its constant term along the unipotent family $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$, computed with the adelic additive Haar measure conditioned on `adelicBox` $K$, vanishes at every $g$; it is $K_f$-smooth, in the sense that its stabiliser in `finiteAdelicGL2Subgroup` $K$ for right translation is open; it is right invariant under $U$; and for every finite place $v$ of $K$ outside $R.\mathrm{exceptionalSet}$ there is a family of $\mathrm{N}(v)+1$ representatives forming a `IsHeckeCosetSystem` for $U$ and `heckeGen` $v$ along which the associated coset sum of $\varphi\ast f$ equals $\Psi.a(v)\cdot(\varphi\ast f)$.
--
--   This is the statement that the Hecke algebra acts on cuspidal automorphic functions by right convolution: convolving a continuous smooth-cusp realisation of a Hecke eigensystem by a factorizable test function supported on (archimedean part) times (principal congruence level group) again yields a cuspidal, $K_f$-smooth, level-invariant function with the same Hecke eigenvalues away from the exceptional set. It is used to show that such convolutions lie in the isotypic cuspidal submodule cut out by the principal level and the archimedean window.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset_principal.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SmoothCusp

theorem AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset_principal
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (Ψ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Ψ)
    (hcont : Continuous R.toFun)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
      glFin (𝓞 K) K a = 1 ∧ k ∈ principalLevel (𝓞 K) K Ψ.level ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) :
    @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
        (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K))
        unipotentGL2 (rightConv K R.toFun f) ∧
      IsKfSmooth K (rightConv K R.toFun f) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ principalLevel (𝓞 K) K Ψ.level ⊓ finiteAdelicGL2Subgroup K,
        rightConv K R.toFun f (g * k) = rightConv K R.toFun f g) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ R.exceptionalSet →
        IsHeckeCosetEigenfunctionAt K (principalLevel (𝓞 K) K Ψ.level ⊓ finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K v) v (rightConv K R.toFun f) (Ψ.a v) := by sorry
