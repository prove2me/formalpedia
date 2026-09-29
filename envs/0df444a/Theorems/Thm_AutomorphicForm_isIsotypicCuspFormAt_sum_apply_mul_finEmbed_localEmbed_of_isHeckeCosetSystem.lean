-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem
-- name    : AutomorphicForm.isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/afa0a3cf-b37b-5624-8b0d-8b2e5ac35c2d
-- title:
--   Local double-coset sums preserve isotypic cusp forms
-- statement:
--   Work over $\mathbb{Q}$ with the pins `productionPinsGeneral ℚ`, i.e. the carrier data consisting of the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the level subgroups $U(N)=\mathrm{levelOne}(N)\cap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathrm{heckeGen}(v)$ and the adelic box. Let $\xi$ be a homomorphism from the central subgroup $Z$ of these pins to $\mathbb{C}^{\times}$, let $N$ be a nonzero ideal of $\mathcal{O}_{\mathbb{Q}}$, let $S$ be a finite set of finite places, and let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex values (a level ideal, nonzero, together with families $a_v,b_v$). Assume $\varphi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ satisfies `IsIsotypicCuspFormAt` for $(\xi,N,S,\Phi)$: it is a $K_f$-smooth cusp automorphic function at the pins with character $\xi$, it is continuous, it is right invariant under $U(N)$, and for every $v\notin S$ it is a Hecke coset eigenfunction for the double coset of $\mathrm{heckeGen}(v)$ modulo $U(N)$ with eigenvalue $\Phi.a\,v$ (there exist $\mathrm{Nm}(v)+1$ representatives forming a coset system whose coset sum multiplies $\varphi$ by $\Phi.a\,v$) and satisfies $\varphi(\mathrm{diag}(\det \mathrm{heckeGen}(v))\,g)=(\mathrm{cNorm}\,v)^{-1}(\Phi.b\,v)\,\varphi(g)$ for all $g$. Fix a finite place $v$, a natural number $m$, elements $\mathrm{loc}_i\in\mathrm{GL}_2(\mathbb{Q}_v)$ for $i\in\mathrm{Fin}\,m$, and $h\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and assume that the adelic elements $r_i=\mathrm{finEmbed}(\mathrm{localEmbed}_v(\mathrm{loc}_i))$ — obtained by splicing $\mathrm{loc}_i$ into the identity at the place $v$ and then the identity at the archimedean places — form a Hecke coset system for $(U(N),h)$, that is: each $r_i$ lies in $U(N)hU(N)$, every element of $U(N)hU(N)$ lies in $r_iU(N)$ for some $i$, and $i\mapsto r_iU(N)$ is injective. Then the function $x\mapsto\sum_{i}\varphi(x\,r_i)$ again satisfies `IsIsotypicCuspFormAt` for the same pins, $\xi$, level $N$ and eigensystem $\Phi$, but with the exceptional set enlarged to $S\cup\{v\}\cup\{w: w\mid N\}$, the last being the finite set of height-one primes occurring in $N$.
--
--   This is the stability of the space of $(\xi,N,\Phi)$-isotypic cusp forms under the double-coset (Hecke-type) operator attached to a coset system supported at a single finite place $v$, at the cost of adding $v$ and the primes dividing $N$ to the set of places where the eigenvalue conditions are not imposed. It is used in the construction of cusp forms with prescribed Whittaker behaviour in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2

open scoped Classical in

theorem AutomorphicForm.isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) (loc : Fin m → GL (Fin 2) (v.adicCompletion ℚ))
    (h : AdelicGL2 (𝓞 ℚ) ℚ)
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsGeneral ℚ).U N) h
      (fun i => finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)))) :
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N
      (S ∪ {v} ∪ (N.finite_factors hN).toFinset) Φ
      (fun x => ∑ i, φ (x * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)))) := by sorry
