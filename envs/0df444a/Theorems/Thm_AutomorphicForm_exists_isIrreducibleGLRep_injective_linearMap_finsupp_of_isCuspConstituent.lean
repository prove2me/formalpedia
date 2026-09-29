-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent
-- name    : AutomorphicForm.exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/57b2a94e-90cb-505c-a5df-c586543dbf3a
-- title:
--   Cuspidal constituents of GL₂/ℚ are isotypic at q
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and let $D=\bigcup_{x\in T}\,\mathfrak S\cdot x$ be the union of the right translates by the members of $T$ of the centre-cut Siegel set $\mathfrak S=$ `centreCutSiegelSet ℚ c u d₁ d₂` (those $g$ whose finite part is integral, each archimedean component having local height at least $c$, $x$-window square at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$). Assume `CoversModCentre` for $D$: every $g$ admits $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and an idele unit $z$ with $\gamma g\,z\in D$. Let the production data `productionPinsOf` be formed from $D$, the level groups $N\mapsto$ `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ` (the latter the kernel of the archimedean projection `glArch`), the Hecke generators `heckeGen` at the finite places, and the adelic box; its centre is the whole idele unit group, and $\xi$ is a character of it. Let $V$ be a complex subspace of the functions $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ which is a cuspidal constituent for these data and $\xi$, i.e. $V$ satisfies the predicate `IsCuspSubrep`, is nonzero, and every subspace $W\le V$ satisfying `IsCuspSubrep` is $\bot$ or $V$. Let $N_0\neq 0$ be an ideal of $\mathbb{Z}$ and $tys_0$ an archimedean type family (a number $\mathrm{card}\,w$ of types `ArchRepAt` at each infinite place $w$), and assume the intersection of $V$ with the space of functions $\varphi$ satisfying $\varphi(gu)=\varphi(g)$ for all $u$ in the level group at $N_0$ and with the archimedean cut $\bigsqcap_w\bigvee_i$ `archTypeSubmoduleAt` of $tys_0$ is nonzero. Then for every prime $q$ there is a complex vector space $W$ with an action of $\mathrm{GL}_2(\mathbb{Q}_q)$ commuting with the scalars, satisfying `IsIrreducibleGLRep q W` (it has a nonzero vector and its only $\mathrm{GL}_2(\mathbb{Q}_q)$-stable complex subspaces are $\bot$ and $\top$), together with an index type $\iota$ and a $\mathbb{C}$-linear map $\Phi$ from [`LocalNewvector.AdelicFnCarrier ℚ`](def/LocalNewvector_AdelicSpanCarrier.html#L13) to the finitely supported functions $\iota\to_{0}W$ such that $\Phi$ kills no nonzero $\psi$ whose underlying function lies in $V$, and $\Phi(x\cdot\psi)=x\cdot\Phi(\psi)$ for all such $\psi$ and all $x\in\mathrm{GL}_2(\mathbb{Q}_q)$.
--
--   This is the $q$-isotypy step in the local–global analysis of cuspidal constituents: a cuspidal constituent containing a nonzero vector of some finite level and of finitely many archimedean types embeds $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariantly into a direct sum of copies of a single irreducible representation $W$ of $\mathrm{GL}_2(\mathbb{Q}_q)$, the local component at $q$. The equivariance and injectivity are asserted only on $V$, so no action on $V$ itself is part of the data; the result is used by [`AutomorphicForm.exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre`](thm.html#AutomorphicForm.exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre) on the way to local newvector theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_LocalNewvector_AdelicSpanCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : IsCuspConstituent ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) ξ V)
    (N₀ : Ideal (𝓞 ℚ)) (hN₀ : N₀ ≠ ⊥) (tys₀ : AutomorphicForm.ArchTypeFamily ℚ)
    (hne : V ⊓ levelInvariantSubmodule ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
          (adelicBox ℚ)) N₀ ⊓ archCutSubmodule ℚ tys₀ ≠ ⊥)
    (q : ℕ) [Fact q.Prime] :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) W)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W),
      LocalNewvector.IsIrreducibleGLRep q W ∧
      ∃ (ι : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι →₀ W)),
        (∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V → Φ ψ = 0 → ψ = 0) ∧
        ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V →
          ∀ x : GL (Fin 2) ℚ_[q], Φ (x • ψ) = x • Φ ψ := by sorry
