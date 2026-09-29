-- Prove2me | Theorems.Thm_AutomorphicForm_memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/e12d778e-b2d9-5591-b71b-7064f0e35122
-- title:
--   Pairings of invariant functions over determinant slabs and the σ-twist
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idèle Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Gal}$-type group $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of $\mathbb{A}_L$, compatible with the diagonal embedding of $L$ and continuous), and let $\sigma$ be a $K$-automorphism of $L$. Let $\alpha, \beta \in \mathbb{R}$ and write $S = \{g \in \mathrm{GL}_2(\mathbb{A}_L) : \|\det g\| \in [\alpha,\beta]\}$, where $\|x\|$ is the module of $x$ acting on $\mathbb{A}_L$ (the value of `distribHaarChar`, as a real number). Let $\Phi_L, \Phi_0 \subseteq S$ be two subsets, each a fundamental domain for the left action of the image of $\mathrm{GL}_2(L)$ in $\mathrm{GL}_2(\mathbb{A}_L)$ on the adelic Haar measure $\mu$ of $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to $S$. Let $u, v : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ satisfy $u(\gamma x) = u(x)$ and $v(\gamma x) = v(x)$ for all $\gamma \in \mathrm{GL}_2(L)$ and all $x$, and suppose $u \in L^2(\mu|_{\Phi_L})$. Then: $u \in L^2(\mu|_{\Phi_0})$; $\int_{\Phi_0} u \bar v \, d\mu = \int_{\Phi_L} u \bar v \, d\mu$; and $\int_{\Phi_0} (u \circ \sigma_{\mathbb{A}}) \overline{(v \circ \sigma_{\mathbb{A}})} \, d\mu = \int_{\Phi_L} u \bar v \, d\mu$, where $\sigma_{\mathbb{A}}$ denotes the automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ induced entrywise by $D.\mathrm{act}\,\sigma$. No integrability hypothesis is imposed on $v$, the Bochner integrals being taken with the usual convention.
--
--   This is the statement that Petersson-type pairings of left $\mathrm{GL}_2(L)$-invariant functions, taken over a fundamental domain inside a slab $\alpha \le \|\det g\| \le \beta$, depend neither on the chosen fundamental domain nor on replacing the functions by their $\sigma$-twists; the inputs are that $\mathrm{GL}_2(L)$ has idèle-norm-one determinants, and that $\sigma_{\mathbb{A}}$ preserves the Haar measure, the slab and the subgroup of global points. It is used in the comparison of convolution operators and of their twisted analogues on the $L^2$ space of the slab quotient, in the base-change part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.memLp_and_setIntegral_mul_conj_eq_and_setIntegral_sigmaSectionActOn_eq_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (ΦL Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (u v : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L γ * x) = u x)
    (hv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L), v (globalPoints (𝓞 L) L γ * x) = v x)
    (hu₂ : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL)) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀) ∧
    (∫ x in Φ₀, u x * conj (v x) ∂adelicGLHaar (Fin 2) (𝓞 L) L =
      ∫ x in ΦL, u x * conj (v x) ∂adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    (∫ x in Φ₀, sigmaSectionActOn K L D σ u x * conj (sigmaSectionActOn K L D σ v x) ∂adelicGLHaar (Fin 2) (𝓞 L) L =
      ∫ x in ΦL, u x * conj (v x) ∂adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
