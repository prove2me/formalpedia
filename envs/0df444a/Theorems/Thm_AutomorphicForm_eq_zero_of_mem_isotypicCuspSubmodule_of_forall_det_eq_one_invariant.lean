-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_mem_isotypicCuspSubmodule_of_forall_det_eq_one_invariant
-- name    : AutomorphicForm.eq_zero_of_mem_isotypicCuspSubmodule_of_forall_det_eq_one_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/72da17a5-020f-5566-9168-fc297a70f94d
-- title:
--   Isotypic cusp forms fixed by SL₂(Kᵥ) vanish
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1K},d_{2K}$ be real numbers and let $T_K$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $K$. Consider the carrier pins `productionPinsOf` for $K$ whose window is the union over $x \in T_K$ of the right translates by $x$ of the centre-cut Siegel set with parameters $c_K,u_K,d_{1K},d_{2K}$ (the set of $g$ whose finite part is integral, each archimedean component having local height at least $c_K$, window square at most $u_K^2$ and archimedean determinant norm in $[d_{1K},d_{2K}]$), whose level family is $N \mapsto \mathrm{principalLevel}(N) \cap \ker(\mathrm{glArch})$, whose Hecke generators are the standard elements `heckeGen` at each finite place, and whose box is the adelic box; these pins carry the Borel structure and adelic Haar measure on $\mathrm{GL}_2$, the full group $Z = \top$ of ideles as centre, and the adelic additive Haar measure conditioned on the box. Let $\xi$ be a homomorphism from that $Z$ to $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_K$, $S$ a finite set of finite places, $\pi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a,b$ of complex numbers indexed by the finite places), $v$ a finite place of $K$, and $\psi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$. Assume $\psi$ lies in the $\mathbb{C}$-span of the functions $\varphi$ that are isotypic cusp forms for these data, i.e. satisfy the predicate `IsSmoothCuspAutomorphicFnAt` for the pins and $\xi$, are continuous, satisfy $\varphi(gu) = \varphi(g)$ for $u$ in the level group at $N$, are Hecke coset eigenfunctions with eigenvalue $\pi.a\,w$ at each $w \notin S$, and satisfy $\varphi(\mathrm{centralScalar}(\det \mathrm{heckeGen}\,w) \cdot g) = \pi.b\,w \cdot \varphi(g)$ for $w \notin S$. Assume further that for every $h \in \mathrm{GL}_2(K_v)$ with $\det h = 1$ and every $x$ one has $\psi(x \cdot \iota_v(h)) = \psi(x)$, where $\iota_v$ places $h$ at $v$ and the identity at all other places and at infinity. Then $\psi = 0$.
--
--   This is the adelic vanishing statement that a cusp form on $\mathrm{GL}_2$ fixed by the determinant-one elements at a single finite place must vanish, a consequence of strong approximation for $\mathrm{SL}_2$ together with cuspidality; here it is stated for arbitrary elements of the span of the isotypic cusp forms at a given level, eigensystem and central character. It is used in the construction of nonzero isotypic cusp forms invariant under a power of the principal level, where it rules out the degenerate case of invariance under all of $\mathrm{SL}_2(K_v)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_mem_isotypicCuspSubmodule_of_forall_det_eq_one_invariant.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.eq_zero_of_mem_isotypicCuspSubmodule_of_forall_det_eq_one_invariant
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ)
    (v : HeightOneSpectrum (𝓞 K)) (ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (hψ : ψ ∈ isotypicCuspSubmodule K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S π)
    (hinv : ∀ h : GL (Fin 2) (v.adicCompletion K), (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 →
      ∀ x : AdelicGL2 (𝓞 K) K, ψ (x * AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v h)) = ψ x) :
    ψ = 0 := by sorry
