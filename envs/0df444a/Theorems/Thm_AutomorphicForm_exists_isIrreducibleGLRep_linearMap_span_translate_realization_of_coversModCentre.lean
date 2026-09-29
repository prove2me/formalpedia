-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre
-- name    : AutomorphicForm.exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/39abc5d6-439f-5d00-8829-b1fbe590ec81
-- title:
--   Cuspidal realisations of Theta embed GL₂(ℚ_q)-equivariantly into one irreducible representation
-- statement:
--   Fix real numbers $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T$ of points of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and put $D=\bigcup_{x\in T} \{g x : g \in \mathcal{S}\}$, where $\mathcal{S}$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (finite part integral, each archimedean local height at least $c$, each archimedean $x$-window square at most $u^2$, each archimedean determinant norm in $[d_1,d_2]$). Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ admits $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and an idele $z$ with $\gamma g z \in D$. Let $\Theta$ be a Hecke eigensystem over $\mathbb{Q}$ with complex eigenvalues $a(v),b(v)$ and nonzero level, and let $q$ be a prime. Write $\mathrm{pins}$ for the production carrier pins over $D$ with level family $N\mapsto \mathrm{levelOne}(N)$ intersected with the kernel of the archimedean projection, Hecke generators $\mathrm{heckeGen}(v)$, and the adelic box as conditioning set. Then there are a type $V$ carrying a complex vector space structure and a distributive action of $\mathrm{GL}_2(\mathbb{Q}_q)$ commuting with the scalars, such that $V\neq 0$ and every $\mathbb{C}$-submodule of $V$ stable under $\mathrm{GL}_2(\mathbb{Q}_q)$ is $0$ or $V$, together with an index type $\iota$ and a $\mathbb{C}$-linear map $L$ from the space of complex functions on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ to $\iota\to_{f} V$ with the following property for every $\psi$ in the $\mathbb{C}$-span of the set of translates $g\cdot R'.\mathrm{toFun}$, where $g\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, $\Theta'$ runs over the Hecke eigensystems whose $a$ and $b$ agree with those of $\Theta$ outside some finite set of finite places, and $R'$ runs over the smooth cusp realisations at $\mathrm{pins}$ for $\Theta'$ whose underlying function is continuous: $L\psi=0$ forces $\psi=0$, and $L(x\cdot\psi)=x\cdot L\psi$ for all $x\in\mathrm{GL}_2(\mathbb{Q}_q)$. Injectivity and equivariance are asserted only for $\psi$ in this span, not on the whole function space.
--
--   This is the adelic form of the statement that all continuous cuspidal realisations sharing a Hecke eigensystem away from finitely many places, and all their right translates, lie in a single irreducible automorphic representation whose component at $q$ is one fixed irreducible smooth representation of $\mathrm{GL}_2(\mathbb{Q}_q)$, occurring with some multiplicity. It feeds the local newvector theory at $q$, and is used by [`AutomorphicForm.exists_isIrreducibleGLRep_injective_linearMap_adelicSpan_finsupp_of_agreesAwayFromFinite`](thm.html#AutomorphicForm.exists_isIrreducibleGLRep_injective_linearMap_adelicSpan_finsupp_of_agreesAwayFromFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_AdelicSpanCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ) (q : ℕ) [Fact q.Prime] :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) V)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V),
      LocalNewvector.IsIrreducibleGLRep q V ∧
      ∃ (ι : Type) (L : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι →₀ V)),
        ∀ ψ ∈ Submodule.span ℂ
            {χ : LocalNewvector.AdelicFnCarrier ℚ |
              ∃ (g : AdelicGL2 (𝓞 ℚ) ℚ) (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
                (R' : SmoothCuspRealizationAt ℚ
                  (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
                    (adelicBox ℚ))
                  Θ')
                (_ : IsGenuineCuspRealizationAt ℚ
                  (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
                    (adelicBox ℚ))
                  Θ' R'),
                χ = g • LocalNewvector.AdelicFnCarrier.mk R'.toFun},
          (L ψ = 0 → ψ = 0) ∧ ∀ x : GL (Fin 2) ℚ_[q], L (x • ψ) = x • L ψ := by sorry
