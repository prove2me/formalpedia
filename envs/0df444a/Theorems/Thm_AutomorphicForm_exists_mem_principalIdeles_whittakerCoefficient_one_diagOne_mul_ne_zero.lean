-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_principalIdeles_whittakerCoefficient_one_diagOne_mul_ne_zero
-- name    : AutomorphicForm.exists_mem_principalIdeles_whittakerCoefficient_one_diagOne_mul_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/6112a3cf-4066-50e5-9f44-0ab735b391de
-- title:
--   Non-vanishing Whittaker coefficient at a principal idele
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$. Fix a subset $D$ of $\mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the ideals of $\mathcal{O}_F$, and a map $\mathrm{gen}$ from the height-one spectrum of $\mathcal{O}_F$ to $\mathrm{GL}_2(\mathbb{A}_F)$; these data, together with the adelic box (the product of a fundamental domain for the Minkowski lattice at the infinite places with the integral finite adeles), assemble into the carrier data `productionPinsOf F D U gen (adelicBox F)`, whose measure on $\mathbb{A}_F$ is the adelic additive Haar measure conditioned on that box, and whose central subgroup is taken to be everything. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is trivial on the image of $F$, continuous and non-trivial, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous, invariant under left translation by the image of $\mathrm{GL}_2(F)$, smooth as a vector for right translation by the kernel of the archimedean projection (the finite part of $\mathrm{GL}_2(\mathbb{A}_F)$), and such that for every $g$ the function $z\mapsto \varphi(u(z)g)$ on the mixed space of $F$, where $u(z)$ is the upper unipotent matrix with entry the adele having infinite part $z$ and zero finite part, is of class $C^{[F:\mathbb{Q}]+1}$. Assume $\varphi$ is cuspidal in the sense that its Whittaker coefficient at $\alpha=0$, namely $\int \varphi(u(x)g)\,d\nu(x)$ for the above conditioned measure $\nu$, vanishes for every $g$. Then for every $g_0$ with $\varphi(g_0)\neq 0$ there is a unit $\gamma$ of $\mathbb{A}_F$ lying in the image of $F^{\times}$ (a principal idele) such that the Whittaker coefficient of $\varphi$ at $\alpha=1$, evaluated at $\mathrm{diag}(\gamma,1)\,g_0$, is non-zero.
--
--   This is the standard non-vanishing consequence of the adelic Fourier–Whittaker expansion of a cusp form on $\mathrm{GL}_2$: a cusp form cannot have all its Whittaker values along the rational diagonal torus translates of a given point equal to zero. It is used in the Langlands–Tunnell part of the argument, to produce a point of the diagonal torus at which the Whittaker coefficient of a cuspidal constituent is non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_principalIdeles_whittakerCoefficient_one_diagOne_mul_ne_zero.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

open scoped Classical in

theorem AutomorphicForm.exists_mem_principalIdeles_whittakerCoefficient_one_diagOne_mul_ne_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hsm : IsKfSmooth F φ)
    (harch : ∀ g : AdelicGL2 (𝓞 F) F,
      ContDiff ℝ (Module.finrank ℚ F + 1) (fun z : mixedEmbedding.mixedSpace F =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0) * g)))
    (hcusp : ∀ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 0 g = 0)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) :
    ∃ γ : (AdeleRing (𝓞 F) F)ˣ, γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F ∧
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne γ * g₀) ≠ 0 := by sorry
