-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero
-- name    : AutomorphicForm.exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/92f2c103-4fa4-517d-a07e-08a4e49771e2
-- title:
--   Non-zero vectors generate the level-and-type subspace of a cuspidal constituent
-- statement:
--   Let $L/K$ be an extension of number fields, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_L)$. Put $\Omega=\bigcup_{x\in T}\{gx : g\in\Sigma\}$, where $\Sigma$ is the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place has local height at least $c$ and window square at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$; assume $\Omega$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(L)$ and $z\in\mathbb{A}_L^\times$ with $\gamma g z\in\Omega$. Let `pins` be the production pins of $L$ with domain $\Omega$, level family $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glFin}^{\mathrm{arch}})$, Hecke generators `heckeGen`, adelic box `adelicBox`, and centre group $\top$, and let $\xi$ be a character of that centre group. Let $N_K\neq 0$ be an ideal of $\mathcal{O}_K$, let $S_K$ be a finite set of primes of $\mathcal{O}_K$ containing every prime dividing $N_K$, let `tys` be an archimedean type family for $L$ (a number of types at each infinite place together with the chosen representations), and let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ which is a cuspidal constituent for $(\mathrm{pins},\xi)$: it satisfies `IsCuspSubrep`, is non-zero, and every `IsCuspSubrep` submodule contained in it is $0$ or $V$. Let $E$ be the intersection of $V$ with the submodule of functions invariant under right multiplication by the level group at $N_K\mathcal{O}_L$ and with $\bigsqcap_w\bigsqcup_i$ the archimedean type submodules given by `tys`. Then for all $y,y'\in E$ with $y\neq 0$ there are a finite set $s$ of functions $\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ and scalars $a(\varphi)\in\mathbb{C}$ such that every $\varphi\in s$ satisfies `IsUnitFactorizableAbove` for $K,L$, the level group at $N_K\mathcal{O}_L$ and $S_K$, satisfies `IsArchBiFinite` for `tys`, and is continuous with compact support, and $y'=\sum_{\varphi\in s}a(\varphi)\cdot \mathrm{rightConv}(y,\varphi)$.
--
--   This is the cyclicity (equivalently, irreducibility under the algebra of admissible test functions) of the space of vectors of fixed level and fixed archimedean types inside a cuspidal constituent: any non-zero such vector generates the whole space by convolutions. It is used in the passage from cuspidal constituents to Hecke eigensystems, being cited by [`AutomorphicForm.exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule`](thm.html#AutomorphicForm.exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V)
    (y y' : AdelicGL2 (𝓞 L) L → ℂ)
    (hy : y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) (hy0 : y ≠ 0)
    (hy' : y' ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
        y' = ∑ φ ∈ s, a φ • convOp L φ y := by sorry
