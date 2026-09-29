-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArithGenuineCuspRealizable_rayClassChar_twist_of_coversModCentre
-- name    : AutomorphicForm.exists_isArithGenuineCuspRealizable_rayClassChar_twist_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/66b0b0a3-daf5-51c9-a4fa-28a85aa025f7
-- title:
--   Twisting a cusp-realizable GL₂ eigensystem by a ray class character
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\,(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\,]$ for the union of the right translates by the elements of $T$ of the centre-cut Siegel set consisting of those $g\in\mathrm{GL}_2(\mathbb{A}_F)$ whose finite component lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at every $w$ lies in $[d_1,d_2]$. Assume `CoversModCentre F D`, i.e. for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele $z\in\mathbb{A}_F^{\times}$ with $\gamma g\,z\in D$. Let $\mathfrak{f}\neq 0$ be an ideal of $\mathcal{O}_F$ and $\chi$ a homomorphism from the narrow ray class group $\mathrm{NarrowRayClassGroup}\,F\,\mathfrak{f}$ (the ideles coprime to the modulus modulo the narrow ray subgroup) to $\mathbb{C}^{\times}$. Let $\pi$ be a Hecke eigensystem over $F$ with complex values, that is, a nonzero level ideal together with tables $a,b$ indexed by the finite places, and assume `IsArithGenuineCuspRealizable F pins π` for the carrier pins $\mathrm{productionPinsOf}\,F\,D\,(N\mapsto \mathrm{levelOne}\,N\sqcap \mathrm{finiteAdelicGL2Subgroup}\,F)\,(v\mapsto \mathrm{heckeGen}\,v)\,(\mathrm{adelicBox}\,F)$, whose measure data are the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, whose fundamental-domain set is $D$, whose central subgroup is the whole of $\mathbb{A}_F^{\times}$, and whose additive measure is Haar measure conditioned on the adelic box; recall that this predicate is genuine cusp-realizability for the renormalised eigensystem $(a_v,\,c_v^{-1}b_v)$. Then there exist a Hecke eigensystem $\pi'$ over $F$ with complex values and a finite set $S$ of finite places such that for every $v\notin S$ with $v\nmid\mathfrak{f}$ one has $a_{\pi'}(v)=\chi([v])\,a_{\pi}(v)$ and $b_{\pi'}(v)=\chi([v])^{2}\,b_{\pi}(v)$, where $[v]=\mathrm{primeClass}\,F\,\mathfrak{f}\,v$, and such that $\pi'$ satisfies `IsArithGenuineCuspRealizable` at the same pins. No assertion is made about the level of $\pi'$.
--
--   This is the twist $\pi\mapsto\pi\otimes(\tilde\chi\circ\det)$ of a cuspidal automorphic form on $\mathrm{GL}_2(\mathbb{A}_F)$ by the finite-order idele class character $\tilde\chi$ attached to a narrow ray class character $\chi$, recorded at the level of Hecke eigensystem tables and only away from a finite set of places. It feeds the base-change and twisting steps used downstream, being cited in the construction of powers and twists of eigensystems compatible with base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArithGenuineCuspRealizable_rayClassChar_twist_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply

theorem AutomorphicForm.exists_isArithGenuineCuspRealizable_rayClassChar_twist_of_coversModCentre
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (χ : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (π : HeckeEigensystem F ℂ)
    (hπ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) π) :
    ∃ π' : HeckeEigensystem F ℂ, ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ v ∉ S, ∀ (hv : ¬ v.asIdeal ∣ 𝔣),
        π'.a v = (χ (primeClass F 𝔣 v hv) : ℂ) * π.a v ∧
        π'.b v = (χ (primeClass F 𝔣 v hv) : ℂ) ^ 2 * π.b v) ∧
      IsArithGenuineCuspRealizable F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) π' := by sorry
