-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero
-- name    : AutomorphicForm.exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d8af6306-03f8-5f86-8890-3ddca210fc24
-- title:
--   Nonzero isotypic cusp form has nonzero archimedean-type component
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1K},d_{2K}$ be reals with $0<c_K$ and $0<d_{1K}<d_{2K}$, and let $T_K$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the set $D=\bigcup_{x\in T_K} (\cdot\,x)''\,\mathrm{centreCutSiegelSet}$ — the union of the right translates by the elements of $T_K$ of the set of $g$ whose finite part is integral, whose archimedean components at every infinite place have local height at least $c_K$, squared window coordinate at most $u_K^2$ and archimedean determinant norm in $[d_{1K},d_{2K}]$ — covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo rational points and the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma g\,z\in D$. Consider the carrier pins `productionPinsOf` attached to $D$, to the level family $N\mapsto$ `principalLevel` $\sqcap$ `finiteAdelicGL2Subgroup`, to the generators $v\mapsto$ `heckeGen`, and to `adelicBox` (whose measure data are the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, whose central subgroup $Z$ is $\top$, and whose adelic measure is additive Haar conditioned on the box). Let $\xi:Z\to\mathbb{C}^\times$ be a character, $S_K$ a finite set of finite places, $N'$ an ideal all of whose prime divisors lie in $S_K$, $\pi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level together with families $a,b$ indexed by finite places), and $u:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ nonzero and `IsIsotypicCuspFormAt` for these data: $u$ is a smooth cuspidal automorphic function for the pins and $\xi$, continuous, invariant under right multiplication by the level subgroup at $N'$, a Hecke coset eigenfunction with eigenvalue $\pi.a\,v$ at each $v\notin S_K$, and satisfies the central relation $u(\mathrm{scalar}(\det \mathrm{heckeGen}\,v)\,g)=(\mathrm{cNorm}\,v)^{-1}\pi.b\,v\cdot u(g)$ for $v\notin S_K$. Then there exist an archimedean type family $\mathrm{tys}$ (a cardinality $\mathrm{card}(w)$ and representations $\mathrm{rep}(w,i)\in$ `ArchRepAt` $K\,w$ for each infinite place $w$) and a function $u'$ which is again isotypic cuspidal for exactly the same pins, $\xi$, $N'$, $S_K$ and $\pi$, lies in $\mathrm{archCutSubmodule}$ of $\mathrm{tys}$, namely $\bigcap_{w}\ \sum_{i<\mathrm{card}(w)} \mathrm{archTypeSubmoduleAt}\,K\,w\,(\mathrm{rep}(w,i))$, and is nonzero.
--
--   This is the step that replaces a nonzero isotypic cusp form by a nonzero component of finite archimedean type, i.e. the extraction of a $K$-type component under the right action of the maximal compact subgroups at the infinite places, with all conditions at the finite places and the central character preserved. It is used by [`AutomorphicForm.exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero`](thm.html#AutomorphicForm.exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero
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
    ∃ (tys : ArchTypeFamily K) (u' : AdelicGL2 (𝓞 K) K → ℂ),
      IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N' SK π u' ∧
      u' ∈ archCutSubmodule K tys ∧ u' ≠ 0 := by sorry
