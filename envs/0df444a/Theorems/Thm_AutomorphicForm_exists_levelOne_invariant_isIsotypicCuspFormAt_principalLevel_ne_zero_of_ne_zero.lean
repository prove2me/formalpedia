-- Prove2me | Theorems.Thm_AutomorphicForm_exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
-- name    : AutomorphicForm.exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/9f262b12-42e4-5e96-8692-5794b90aa8bb
-- title:
--   Nonzero isotypic cusp form invariant under a level-one subgroup
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1K},d_{2K}$ be real numbers with $0<c_K$, $0<d_{1K}<d_{2K}$, and let $T_K$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$. Write $D$ for the union over $x\in T_K$ of the right translates by $x$ of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K`, i.e. of those $g$ whose finite component is integral, whose archimedean components have local height at least $c_K$ and window square at most $u_K^2$ at every infinite place, and whose archimedean determinant norms all lie in $[d_{1K},d_{2K}]$; it is assumed that $D$ covers $\mathrm{GL}_2$ of the adeles modulo left multiplication by global points and right multiplication by central adelic scalars. The carrier data are `productionPinsOf` for this $D$, for the level groups $N\mapsto \mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, for the Hecke generators `heckeGen`, and for the adelic box; in particular its central subgroup is all of $(\mathbb{A}_K)^\times$, and $\xi$ is an arbitrary homomorphism from that group to $\mathbb{C}^\times$. Let $S_K$ be a finite set of finite places, $N'$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, $\pi$ a Hecke eigensystem over $\mathbb{C}$, and $u\neq 0$ a function on $\mathrm{GL}_2$ of the adeles which is an isotypic cusp form for these data at level $N'$: a continuous smooth cuspidal automorphic function with central character $\xi$, right invariant under $\mathrm{principalLevel}(N')\sqcap\mathrm{finiteAdelicGL2Subgroup}$, a Hecke coset eigenfunction with eigenvalue $\pi.a\,v$ at each $v\notin S_K$, and satisfying the central relation with eigenvalue $(\mathrm{cNorm}\,v)^{-1}\pi.b\,v$ there. Then there exist a nonzero ideal $N''$, again with all prime divisors in $S_K$, and a function $\varphi\neq 0$ which is an isotypic cusp form for the same $\xi$, $S_K$ and $\pi$ at level $N''$ and is in addition right invariant under the larger group $\mathrm{levelOne}(N'')\sqcap\mathrm{finiteAdelicGL2Subgroup}$. No divisibility relation between $N''$ and $N'$ is asserted.
--
--   This is the passage from a principal congruence level to a level-one ($U_1$-type) invariant vector inside the same isotypic cuspidal family, the global form of the local new-vector theory of Atkin–Lehner type. It feeds the comparison of cusp classes at principal and level-one structures, [`AutomorphicForm.exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel`](thm.html#AutomorphicForm.exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (π : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N' SK π u)
    (hu0 : u ≠ 0) :
    ∃ (N'' : Ideal (𝓞 K)) (φ : AdelicGL2 (𝓞 K) K → ℂ),
      N'' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N'' → v ∈ SK) ∧
      IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N'' SK π φ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ x ∈ levelOne (𝓞 K) K N'' ⊓ finiteAdelicGL2Subgroup K, φ (g * x) = φ g) ∧
      φ ≠ 0 := by sorry
