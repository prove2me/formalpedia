-- Prove2me | Theorems.Thm_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
-- name    : AutomorphicForm.exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/6f98310c-8c24-57fc-95cf-eb78b590c9a8
-- title:
--   One-prime step towards U₁-invariance at principal level
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1K},d_{2K}$ be reals with $c_K>0$, $0<d_{1K}<d_{2K}$, and let $T_K$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$; write $D_K=\bigcup_{x\in T_K}(\cdot\,*x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K`, the union of the right translates by the elements of $T_K$ of the set of $g$ whose finite part is integral, whose archimedean components at every infinite place have local height at least $c_K$, have $x$-window square at most $u_K^2$, and have archimedean determinant norm in $[d_{1K},d_{2K}]$; assume `CoversModCentre K D_K`, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma g\,z\in D_K$. Let `pins` be `productionPinsOf K D_K` with level groups $N\mapsto$ `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (the intersection of $\mathrm{levelOne}(N)$ with its conjugate by the Weyl element, cut down to the kernel of the archimedean projection), Hecke generators `heckeGen (𝓞 K) K v`, and box `adelicBox K`; let $\xi:\mathrm{pins}.Z\to\mathbb{C}^\times$ be a character of its central group (which is all of the idele units). Let $S$ be a finite set of finite places, $\pi$ a Hecke eigensystem over $\mathbb{C}$, `tys` an archimedean type family, $v\in S$, $D,E_0$ ideals of $\mathcal{O}_K$, $k\in\mathbb{N}$, and $\varphi$ a complex function on $\mathrm{GL}_2$ of the adeles such that: $\varphi$ is an `IsIsotypicCuspFormAt` form for these pins, $\xi$, level $D\,E_0\,v^k$, $S$ and $\pi$ (that is, it is a smooth cusp automorphic function for $\xi$, continuous, right invariant under the level group at $D\,E_0\,v^k$, a Hecke coset eigenfunction with eigenvalue $\pi.a(w)$ for every $w\notin S$, and satisfies $\varphi(\mathrm{diag}(\det\,\mathrm{gen}(w))\,g)=(\mathrm{cNorm}\,w)^{-1}\pi.b(w)\,\varphi(g)$ for $w\notin S$); $\varphi$ is right invariant under `levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K`; $\varphi$ lies in `archCutSubmodule K tys`, the infimum over infinite places $w$ of the supremum of the archimedean type submodules attached to the finitely many representations `tys.rep w i`; and $\varphi\neq 0$. Then there are $c\in\mathbb{N}$ and a function $\varphi'$ which is an isotypic cusp form for the same pins, $\xi$, $S$ and $\pi$ at level $D\,v^c\,E_0$, is right invariant under `levelOne (𝓞 K) K (D * v.asIdeal ^ c) ⊓ principalLevel (𝓞 K) K E₀ ⊓ finiteAdelicGL2Subgroup K`, lies in `archCutSubmodule K tys`, and is nonzero.
--
--   This is the one-prime induction step that converts principal congruence invariance at a prime $v$ into $U_1$-type invariance at $v$ at the cost of an exponent $c$ (the conductor of the local constituent at $v$), in the spirit of Casselman's theory of new vectors; the primes dividing $D$ have already been moved, those dividing $E_0$ remain at principal level. It is used by [`AutomorphicForm.exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero`](thm.html#AutomorphicForm.exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero), which iterates the step over all primes of the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ) (tys : ArchTypeFamily K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (D E₀ : Ideal (𝓞 K)) (k : ℕ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ (D * E₀ * v.asIdeal ^ k) S π φ)
    (hφD : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
        φ (g * x) = φ g)
    (hφt : φ ∈ archCutSubmodule K tys) (hφ0 : φ ≠ 0) :
    ∃ (c : ℕ) (φ' : AdelicGL2 (𝓞 K) K → ℂ),
      IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ (D * v.asIdeal ^ c * E₀) S π φ' ∧
      (∀ g : AdelicGL2 (𝓞 K) K,
        ∀ x ∈ levelOne (𝓞 K) K (D * v.asIdeal ^ c) ⊓ principalLevel (𝓞 K) K E₀ ⊓ finiteAdelicGL2Subgroup K,
          φ' (g * x) = φ' g) ∧
      φ' ∈ archCutSubmodule K tys ∧ φ' ≠ 0 := by sorry
