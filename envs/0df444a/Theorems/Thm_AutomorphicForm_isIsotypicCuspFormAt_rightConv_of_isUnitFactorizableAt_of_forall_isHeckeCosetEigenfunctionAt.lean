-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
-- name    : AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/0511107c-1696-5a6e-98dd-d33db9ce01f3
-- title:
--   Right convolution preserves isotypic cusp forms and archimedean cuts
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1K},d_{2K}$ be reals with $c_K>0$, $0<d_{1K}<d_{2K}$, let $T_K$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and assume the union $D=\bigcup_{x\in T_K}(\cdot\,x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K` (the set of $g$ whose finite part is integral and which at every infinite place satisfy $\mathrm{localHeight}\ge c_K$, $\mathrm{xWindowSq}\le u_K^2$ and $\mathrm{archDetNorm}\in[d_{1K},d_{2K}]$) covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left translation by $\mathrm{GL}_2(K)$ and right translation by central ideles. Let $UB$ assign a subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ to each ideal, let $\xi$ be a character of the central subgroup of the carrier data `productionPinsOf` built from $D$, the levels $N\mapsto$ `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, the generators `heckeGen`, and the box `adelicBox K` (this subgroup being $\top$, hence the same for every level family), let $N,N''$ be ideals, $S$ a finite set of primes containing all prime divisors of $N$, $\pi$ a Hecke eigensystem over $\mathbb{C}$, and let $u$ be an isotypic cusp form for $\xi$, $N$, $S$, $\pi$ at those principal levels: smooth and cuspidal for $\xi$, $K_f$-smooth, continuous, right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, a Hecke coset eigenfunction with eigenvalue $\pi.a\,v$ for `heckeGen (𝓞 K) K v` at each $v\notin S$, and with central relation given by $(\mathrm{cNorm}\,v)^{-1}\pi.b\,v$. Assume further that for every $v\notin S$ there are $\mathrm{absNorm}(v)+1$ elements $r_i\in\mathrm{GL}_2(K_v)$ whose images in $\mathrm{GL}_2(\mathbb{A}_K)$ under [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) followed by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) form, simultaneously, a complete irredundant system of coset representatives for the double coset of `heckeGen (𝓞 K) K v` relative to `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and relative to $UB(N'')$. Let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfy `IsUnitFactorizableAt K ⊥ S f`, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ a compactly supported smooth function of the matrix entries, $f_{\mathrm{fin}}$ locally constant with compact support, local test functions $f_v$ for $v\in S$ such that $f_{\mathrm{fin}}(h)=\prod_{v\in S}f_v(h_v)$ when $h_v$ is integral at all $v\notin S$ and $f_{\mathrm{fin}}(h)=0$ otherwise (bi-invariance under the trivial subgroup being vacuous). Assume also that $f(xg)=f(g)$ for all $x\in UB(N'')$, and that $f$ is invariant under conjugation by `rowIsometryInclAt₀ K w k` for every infinite place $w$ and every $k$ in the row-isometry subgroup of $\mathrm{GL}_2(K_w)$. Then the right convolution $g\mapsto\int u(gx)f(x)\,dx$ against the adelic Haar measure is an isotypic cusp form for $\xi$, $N''$, $S$, $\pi$ with respect to the same carrier data but with level family $UB$; moreover, for every archimedean type family $\mathrm{tys}$, if $u$ lies in the associated archimedean cut submodule then so does the convolution.
--
--   This is the standard statement that right convolution against a factorizable test function which is left invariant under a level group, and whose archimedean part is invariant under conjugation by the maximal compact subgroups, carries an isotypic cusp form of one level to an isotypic cusp form of the new level with the same Hecke eigensystem and central character, while preserving prescribed archimedean types. It is the transfer step used when producing nonzero isotypic cusp forms invariant under a prescribed level subgroup and lying in a prescribed archimedean cut; no nonvanishing of the convolution is asserted here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt.lean

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

theorem AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (UB : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N N'' : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (π : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S π u)
    (hsys : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ r : Fin (Ideal.absNorm v.asIdeal + 1) → GL (Fin 2) (v.adicCompletion K),
        HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (heckeGen (𝓞 K) K v) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (r i))) ∧
          HeckeIntegralSeam.IsHeckeCosetSystem (UB N'') (heckeGen (𝓞 K) K v)
            (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (r i))))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsUnitFactorizableAt K ⊥ S f)
    (hfL : ∀ x ∈ UB N'', ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g)
    (hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) :
    IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          UB (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        ξ N'' S π (rightConv K u f) ∧
      ∀ tys : ArchTypeFamily K, u ∈ archCutSubmodule K tys → rightConv K u f ∈ archCutSubmodule K tys := by sorry
