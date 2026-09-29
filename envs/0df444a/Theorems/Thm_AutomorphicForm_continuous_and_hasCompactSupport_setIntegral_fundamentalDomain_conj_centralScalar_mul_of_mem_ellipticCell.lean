-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell
-- name    : AutomorphicForm.continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9f8b141a-6896-5ff4-af40-44dca6b0d64a
-- title:
--   Continuity and compact support of truncated elliptic orbital integrals
-- statement:
--   Let $F$ be a number field, with $\mathcal O_F$ its ring of integers and adele ring $\mathbb A_F$; the group $GL_2(\mathbb A_F)$ carries its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, and centralizer subgroups carry their Borel $\sigma$-algebras. Let $\alpha,\beta$ be reals with $0<\alpha$, and let $\gamma_0\in GL_2(F)$ lie in `ellipticCell`, i.e. the characteristic polynomial of the underlying $2\times 2$ matrix over $F$ has no root in $F$. Write $\iota$ for `globalPoints`, the homomorphism $GL_2(F)\to GL_2(\mathbb A_F)$ induced by $F\to\mathbb A_F$, and let the determinant slab be $\{g: \|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is `ideleNorm`, the value at an idele of the distributive Haar character of $\mathbb A_F$, read as a real number. Let $\Psi\subseteq GL_2(\mathbb A_F)$ be contained in this slab and be a fundamental domain, for the Haar measure restricted to the slab, for the left translation action of the image under $\iota$ of the centralizer of $\{\gamma_0\}$ in $GL_2(F)$. Let $f:GL_2(\mathbb A_F)\to\mathbb C$ be continuous with compact support. Then the function sending an idele $z\in\mathbb A_F^\times$ to $\int_\Psi f\bigl(x^{-1}\,\iota(\gamma_0)\,(z\cdot 1_2)\,x\bigr)\,dx$, with $z$ embedded as a central scalar matrix via `centralScalar` and the integral taken against the Haar measure, is both continuous and compactly supported.
--
--   This is the statement that the elliptic orbital integral of a test function, truncated to a fundamental domain inside a determinant slab, depends on the central idele parameter through a continuous function of compact support; it is the analytic input that makes the elliptic contribution to the adelic trace formula for $GL_2$ amenable to integration over the central idele class group. It is used in the computation of the elliptic term as a product of a centralizer volume with a sum of orbital integrals over conjugacy classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α)
    (γ₀ : GL (Fin 2) F) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell F)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
    HasCompactSupport (fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) := by sorry
