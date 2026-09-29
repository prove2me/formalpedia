-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable
-- name    : AutomorphicForm.exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/7619f433-c8af-5e1a-9dfa-cf0f38035ff1
-- title:
--   Cusp-realizable eigensystem realised in a single cuspidal constituent
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in the integral subset `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height at least $c$ and squared $x$-window at most $u^2$, and with `archDetNorm` $w$ $g\in[d_1,d_2]$. Assume `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ can be written so that $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(K)$ (via `globalPoints`) and some central scalar $z$ from $(\mathbb{A}_K)^\times$. Let $\mathrm{pins}$ be `productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, i.e. the carrier data with measurable structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, fundamental-type region $D$, centre $Z=\top$, level groups the intersections of $\mathrm{levelOne}(N)$ with the kernel of the archimedean projection, the standard Hecke generators at finite places, and the additive Haar measure conditioned on the adelic box. Let $\Theta$ be a complex Hecke eigensystem over $K$ (a non-zero level ideal $\Theta.\mathrm{level}$ together with families $a_v,b_v\in\mathbb{C}$ indexed by the finite places), and assume `IsArithGenuineCuspRealizable K pins Θ`, that is `IsGenuineCuspRealizable` for $\mathrm{pins}$ and the raw central datum of $\Theta$. Then there exist a character $\xi\colon Z\to\mathbb{C}^\times$, a finite set $S$ of finite places of $K$, an archimedean type family $\mathrm{tys}$ (for each infinite place $w$ a number $\mathrm{card}\,w$ of archimedean representations $\mathrm{rep}\,w\,i$), a $\mathbb{C}$-submodule $V$ of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and a function $\varphi$ such that: $V$ is a cuspidal constituent for $(\mathrm{pins},\xi)$, i.e. $V$ satisfies `IsCuspSubrep`, $V\neq 0$, and every $W$ satisfying `IsCuspSubrep` with $W\le V$ is $0$ or $V$; $\varphi\in V$ and $\varphi\neq 0$; $\varphi$ is an isotypic cusp form at $(\xi,\Theta.\mathrm{level},S,\Theta)$, meaning $\varphi$ is a smooth cuspidal automorphic function for $(\mathrm{pins},\xi)$, continuous, right invariant under the level group at $\Theta.\mathrm{level}$, a Hecke coset eigenfunction with eigenvalue $a_v$ at every $v\notin S$, and satisfies $\varphi(\mathrm{diag}(\det \mathrm{gen}_v)\,g)=b_v\varphi(g)$ for all $g$ and all $v\notin S$; and $\varphi$ lies in `archCutSubmodule K tys`, the intersection over infinite places $w$ of the sums of the archimedean type submodules attached to the $\mathrm{rep}\,w\,i$.
--
--   This is the passage, at the level of functions and without any multiplicity statement, from a genuinely cusp-realizable Hecke eigensystem to an actual non-zero cusp form that has finitely many archimedean types and lies inside a single irreducible (minimal non-zero) constituent of the cuspidal spectrum. It is used in the project as the input to the analytic study of the associated $L$-function, being cited by the results producing the Euler-product and meromorphic-continuation statements for `rsEulerPoly`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
      (S : Finset (HeightOneSpectrum (𝓞 K))) (tys : AutomorphicForm.ArchTypeFamily K)
      (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (φ : AdelicGL2 (𝓞 K) K → ℂ),
      IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V ∧ φ ∈ V ∧ φ ≠ 0 ∧
        IsIsotypicCuspFormAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ Θ.level S Θ φ ∧ φ ∈ archCutSubmodule K tys := by sorry
