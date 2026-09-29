-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel
-- name    : AutomorphicForm.exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e00388e0-6300-5173-840d-18ef4f171dd2
-- title:
--   Principal congruence cuspidal classes descend to `levelOne` classes
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1K},d_{2K}$ be reals with $c_K>0$, $0<d_{1K}<d_{2K}$, and let $T_K$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$. Write $D=\bigcup_{x\in T_K}(\cdot\,x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K`, the union of the right translates by elements of $T_K$ of the set of $g$ whose finite part is integral, whose archimedean components have local height $\ge c_K$ and $x$-window square $\le u_K^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$; assume `CoversModCentre K D`, i.e. every adelic $g$ can be moved into $D$ by left multiplication by a $K$-rational point and right multiplication by a central idelic scalar. Let $S_K$ be a finite set of finite places. Both carrier data are `productionPinsOf` for this $D$, the Hecke generators `heckeGen`, the box `adelicBox K`, and the central subgroup $\top$, differing only in the level family: $N\mapsto$ `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` in the first, $N\mapsto$ `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` in the second (note `principalLevel` is `levelOne` intersected with its Weyl conjugate, hence the smaller group). Let $\xi_K$ be a homomorphism from the central subgroup of the first datum to $\mathbb{C}^\times$, let $N'$ be an ideal all of whose prime divisors lie in $S_K$, and let $\pi$ be a Hecke eigensystem over $\mathbb{C}$ lying in `cuspClasses` for the principal-level datum with data $\xi_K,N',S_K$: that is, $\pi.\mathrm{level}=N'$, $\pi.a\,v=\pi.b\,v=0$ for all $v\in S_K$, and the span of the functions satisfying the project's predicate `IsIsotypicCuspFormAt` for these data is nonzero. Then there exist an ideal $N''\neq\bot$ all of whose prime divisors lie in $S_K$ and a Hecke eigensystem $\pi''$ over $\mathbb{C}$ lying in `cuspClasses` for the `levelOne` datum with data $\xi_K,N'',S_K$, such that $\pi''.a\,v=\pi.a\,v$ and $\pi''.b\,v=\pi.b\,v$ for every $v\notin S_K$. Only existence is asserted; no bound on $N''$ is given.
--
--   This is the level-change step replacing invariance under a principal congruence subgroup by invariance under a group of $U_1$-type (`levelOne`) inside the same cuspidal constituent, the adelic counterpart of the theory of new vectors and conductors of Atkin–Lehner–Casselman type, with the Hecke eigenvalues away from the auxiliary set $S_K$ preserved. It feeds the construction of cuspidal classes at $U_1$-levels used downstream, in particular in the passage to arithmetically genuine realisable cusp forms and in the table/box statements for Siegel windows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (π : HeckeEigensystem K ℂ)
    (hπ : π ∈ cuspClasses K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξK N' SK) :
    ∃ (N'' : Ideal (𝓞 K)) (π'' : HeckeEigensystem K ℂ),
      N'' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N'' → v ∈ SK) ∧
      π'' ∈ cuspClasses K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK N'' SK ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → π''.a v = π.a v ∧ π''.b v = π.b v) := by sorry
