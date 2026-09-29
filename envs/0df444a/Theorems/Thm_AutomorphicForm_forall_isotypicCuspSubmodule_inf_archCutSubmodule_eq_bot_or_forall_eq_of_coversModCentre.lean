-- Prove2me | Theorems.Thm_AutomorphicForm_forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre
-- name    : AutomorphicForm.forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/875cb218-40aa-5ca1-81aa-c1920d419ba1
-- title:
--   Dichotomy for type-cut isotypic cusp spaces over a covering Siegel window
-- statement:
--   Let $F$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha<\beta$. Let $S$ be a set of adelic points of $\mathrm{GL}_2$ over $F$ contained in the determinant slab $\{g : \|\det g\|_{\mathbb A}\in[\alpha,\beta]\}$, where $\|\cdot\|_{\mathbb A}$ is the idele norm given by the module of the distributive Haar character, and assume $S$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(F)$ under `globalPoints` with respect to the adelic Haar measure `adelicGLHaar` restricted to that slab. Let $\xi$ be a character of the centre group of the carrier data `productionPinsOf`, i.e. a homomorphism from the full unit group of the adele ring to $\mathbb C^\times$; the carrier data attaches to a set $D$ the Borel structure and Haar measure on adelic $\mathrm{GL}_2$, the domain $D$, the full centre, the level subgroups $N\mapsto \mathrm{levelOne}(N)$ intersected with the kernel of the archimedean projection, the Hecke generators `heckeGen` at finite places, and the additive Haar measure on the adeles conditioned on the box `adelicBox` (infinite box times integral finite adeles). Let $c,u,d_1,d_2$ be reals with $d_1<d_2$, let $T$ be a finite set of adelic points, and put $W=\bigcup_{x\in T}\,\{g\cdot x : g\in \mathfrak S\}$ where $\mathfrak S$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$: those $g$ whose finite part is integral and whose archimedean components at every infinite place $w$ have local height at least $c$, squared $x$-window at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$. Assume $W$ covers modulo the centre: for every adelic $g$ there are $\gamma\in\mathrm{GL}_2(F)$ and an adelic idele $z$ with $\gamma g\,z\in W$ (the central scalar acting on the right). The conclusion is a dichotomy holding uniformly in all remaining data: either for every ideal $N$ of $\mathcal O_F$, every finite set $P$ of finite places, every archimedean type family `tys` and every Hecke eigensystem $\Psi$ over $\mathbb C$, the isotypic cusp submodule (the $\mathbb C$-span of the functions satisfying `IsIsotypicCuspFormAt` for the carrier data with domain $W$, character $\xi$, level $N$, places $P$ and eigensystem $\Psi$) intersected with the type-cut submodule $\bigsqcap_w \bigvee_{i<\mathrm{card}(w)}$ of the archimedean type submodules of `tys` is zero; or, for all such $N,P,\mathrm{tys},\Psi$, that intersection coincides with the corresponding intersection formed from the carrier data with domain $S$ instead of $W$.
--
--   This compares the spaces of isotypic cusp forms cut by archimedean types according to whether the square-integrability condition is read on a finite union of right translates of a centre-cut Siegel set or on a fundamental domain of a determinant slab, asserting that the two agree across all levels, eigensystems and type families unless all the cut spaces vanish. It is used in the study of twisted cut traces, being cited by [`AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime`](thm.html#AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime) and [`AutomorphicForm.exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime`](thm.html#AutomorphicForm.exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
AutomorphicForm.forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : AutomorphicForm.SiegelCovering.CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    (∀ (N : Ideal (𝓞 F)) (P : Finset (HeightOneSpectrum (𝓞 F))) (tys : ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ),
        (isotypicCuspSubmodule F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)) ξ N P Ψ
          ⊓ archCutSubmodule F tys) = ⊥) ∨
    (∀ (N : Ideal (𝓞 F)) (P : Finset (HeightOneSpectrum (𝓞 F))) (tys : ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ),
        (isotypicCuspSubmodule F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)) ξ N P Ψ
          ⊓ archCutSubmodule F tys) =
          (isotypicCuspSubmodule F
              (productionPinsOf F S
                (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
                (adelicBox F)) ξ N P Ψ
            ⊓ archCutSubmodule F tys)) := by sorry
