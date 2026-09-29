-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain
-- name    : AutomorphicForm.exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/24289f86-4470-5a10-85d5-bd6dab580e3f
-- title:
--   Right convolution realises every endomorphism of an isotypic cusp space
-- statement:
--   Let $K \subseteq L$ be number fields, let $0 < \alpha < \beta$ be reals, and let $S$ be a subset of the determinant slab $\{g \in \mathrm{GL}_2(\mathbb{A}_L) : \|\det g\|_{\mathbb{A}} \in [\alpha,\beta]\}$, where the norm is the module of the idele acting on the adeles, which is a fundamental domain for the image subgroup $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ with respect to the Haar measure `adelicGLHaar` restricted to that slab. Form the carrier pins `productionPinsOf L S` with the level family $N \mapsto$ `levelOne` $(N) \sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen`, and the box `adelicBox L`; their centre group is all of $(\mathbb{A}_L)^{\times}$, and $\xi$ is a character of it with values in $\mathbb{C}^{\times}$. Let $N_K$ be an ideal of $\mathcal{O}_K$, $S_K$ a finite set of primes of $K$ containing every prime dividing $N_K$, $S_L$ a finite set of primes of $L$, $\Psi$ a Hecke eigensystem for $L$ over $\mathbb{C}$ (a nonzero level ideal together with families $a, b$ of complex numbers indexed by the primes of $L$), and `tys` an archimedean type family for $L$ (for each infinite place $w$ a finite list of representations of the relevant row-isometry group). Let $V$ be a $\mathbb{C}$-subspace of the functions $\mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ contained in the intersection of `archCutSubmodule L tys`, the infimum over infinite places $w$ of the supremum of the type submodules attached to the representations `tys.rep w i`, with the span of the functions $\varphi$ satisfying `IsSmoothCuspAutomorphicFnAt` for these pins and $\xi$, continuous, invariant under right translation by `levelOne` $(N_K\mathcal{O}_L) \sqcap$ `finiteAdelicGL2Subgroup`, a Hecke coset eigenfunction with eigenvalue $\Psi.a\,v$ at each prime $v \notin S_L$, and satisfying $\varphi(z(\det(\mathrm{heckeGen}\, v))g) = \Psi.b\,v \cdot \varphi(g)$ for $v \notin S_L$ and all $g$. Then for every $\mathbb{C}$-linear endomorphism $f$ of $V$ there are a finite set $s$ of functions on $\mathrm{GL}_2(\mathbb{A}_L)$ and complex coefficients $c$ such that each $\varphi \in s$ is continuous, compactly supported, and unit-factorizable above $K$ of type `tys` relative to $S_K$ and the level `levelOne` $(N_K\mathcal{O}_L) \sqcap$ `finiteAdelicGL2Subgroup` (bi-invariant under that subgroup, admitting a semi-local factorization over $S_K$, and archimedean bi-finite for `tys`), and such that for every $v \in V$ one has $f(v) = \sum_{\varphi \in s} c_\varphi \, (g \mapsto \int v(gx)\varphi(x)\,dx)$ as functions on $\mathrm{GL}_2(\mathbb{A}_L)$.
--
--   This is the surjectivity of the action of the convolution algebra of suitable test functions on a finite-dimensional space of isotypic cusp forms on $\mathrm{GL}_2$ over $L$: every linear endomorphism of a subspace is realised by a finite linear combination of right convolutions by continuous compactly supported functions that are unit-factorizable above $K$. It is the version of the statement phrased for a fundamental domain of a determinant-norm slab, and is used to obtain the corresponding statement for Siegel sets covering modulo the centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_finset_convOp_eq_of_le_isotypicCuspSubmodule_inf_archCutSubmodule_of_isFundamentalDomain
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (S : Set (AdelicGL2 (𝓞 L) L))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 L) L).range S
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf L S
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : V ≤ isotypicCuspSubmodule L
          (productionPinsOf L S
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys)
    (f : Module.End ℂ V) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (c : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
      ∀ v : V, ((f v : V) : AdelicGL2 (𝓞 L) L → ℂ) = ∑ φ ∈ s, c φ • convOp L φ (v : AdelicGL2 (𝓞 L) L → ℂ) := by sorry
