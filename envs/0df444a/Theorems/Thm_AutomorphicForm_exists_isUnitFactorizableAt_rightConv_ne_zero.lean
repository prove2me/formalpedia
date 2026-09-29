-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isUnitFactorizableAt_rightConv_ne_zero
-- name    : AutomorphicForm.exists_isUnitFactorizableAt_rightConv_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e94a48a0-573d-5cc2-9c83-776f6c7d4175
-- title:
--   Nonzero right convolution against a unit-factorizable test function
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1K},d_{2K}$ be reals and $T_K$ a finite subset of $\mathrm{GL}_2$ of the adeles of $K$; form the carrier data `productionPinsOf` for $K$ whose window is the union over $x\in T_K$ of the right translates by $x$ of `centreCutSiegelSet K cK uK d₁K d₂K` (finite part integral, local heights $\ge c_K$, $x$-window bounded by $u_K^2$, archimedean determinant norms in $[d_{1K},d_{2K}]$), whose level family is $N\mapsto$ `principalLevel` at $N$ intersected with the kernel of the archimedean projection, whose Hecke elements are `heckeGen` at each finite place, and whose box is `adelicBox K`; since the centre subgroup of these data is $\top$, $\xi$ is a character of the full idele unit group. Let $S$ be a finite set of finite places, $\pi$ a Hecke eigensystem over $\mathbb{C}$, $v$ a finite place, $D,E_0$ ideals, $k\in\mathbb{N}$, and $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$. Assume $\varphi$ satisfies `IsIsotypicCuspFormAt` for these data, $\xi$, level $D\,E_0\,v^k$, $S$ and $\pi$ (smooth cuspidal automorphic for the window and measure, continuous, right invariant under the level group at $D\,E_0\,v^k$, a coset Hecke eigenfunction with eigenvalue $\pi.a(w)$ for each $w\notin S$, and central eigenvalue $(\mathrm{cNorm}\,w)^{-1}\pi.b(w)$ on the scalars $\det(\mathrm{heckeGen}_w)$), that $\varphi$ is right invariant under $\mathrm{levelOne}(D)\cap\mathrm{principalLevel}(E_0v^k)$ intersected with the finite-adelic subgroup, and that $\varphi\ne 0$. Then there is $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is `IsUnitFactorizableAt` for the trivial subgroup $\bot$ and $S$ (so $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ an archimedean test factor, $f_{\mathrm{fin}}$ a finite test factor equal to $\prod_{w\in S}f_w(g_w)$ when all components outside $S$ are locally integral and $0$ otherwise, each $f_w$ a local test function), is left invariant under the same group $\mathrm{levelOne}(D)\cap\mathrm{principalLevel}(E_0v^k)$ intersected with the finite-adelic subgroup, is invariant under conjugation by the images under `rowIsometryInclAt₀` of the project's subgroups `rowIsometrySubgroup₀` at every infinite place, and satisfies $\mathrm{rightConv}_K(\varphi,f)\ne 0$, i.e. $g\mapsto\int\varphi(gx)f(x)\,d\mu(x)$ is not identically zero for the adelic Haar measure.
--
--   This is the approximate-identity step for the adelic convolution algebra: a nonzero isotypic cusp form is not annihilated by right convolution with some factorizable test function of the prescribed invariance type. It is used in the construction of a nonzero isotypic cusp form invariant under a power of a level-one group inside a principal level group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isUnitFactorizableAt_rightConv_ne_zero.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_isUnitFactorizableAt_rightConv_ne_zero
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ)
    (v : HeightOneSpectrum (𝓞 K))
    (D E₀ : Ideal (𝓞 K)) (k : ℕ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ (D * E₀ * v.asIdeal ^ k) S π φ)
    (hφD : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
        φ (g * x) = φ g)
    (hφ0 : φ ≠ 0) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsUnitFactorizableAt K ⊥ S f ∧
      (∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
        ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) ∧
      (∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) ∧
      rightConv K φ f ≠ 0 := by sorry
