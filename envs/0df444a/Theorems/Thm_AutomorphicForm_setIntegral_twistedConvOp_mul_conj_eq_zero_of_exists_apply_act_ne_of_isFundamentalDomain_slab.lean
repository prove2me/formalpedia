-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b18d3522-9112-5796-b332-d5b5d8bb7966
-- title:
--   Vanishing of twisted convolution pairing for non-σ-invariant central character
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be a Galois descent datum for the adeles of $L$ over $K$, that is, a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from the $K$-automorphisms of $L$ to the continuous ring automorphisms of $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L` satisfying $D.\mathrm{act}\,\sigma$ applied to a principal adele $x \in L$ equals $\sigma(x)$, and let $\sigma : L \simeq_K L$. Let $\alpha, \beta \in \mathbb{R}$ and write $S = \{g \in \mathrm{GL}_2(\mathbb{A}_L) : \|\det g\| \in [\alpha,\beta]\}$ for the determinant slab, the norm being [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the value of the distributive Haar character of $\mathbb{A}_L$ at an idele. Let $\Phi_L$ be a fundamental domain for the left action of the image of $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ on the adelic Haar measure `adelicGLHaar` restricted to $S$, and let $\Phi_0 \subseteq S$ be a second such fundamental domain. Let $\xi_L$ be a homomorphism from the full group of ideles $\mathbb{A}_L^\times$ (as the subgroup $\top$) to $\mathbb{C}^\times$, no continuity being assumed, and assume $\xi_L$ is not $\sigma$-invariant: there is an idele $z$ with $\xi_L(D.\mathrm{act}\,\sigma(z)) \neq \xi_L(z)$. Let $u, v : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ both satisfy `IsLsXiFunction`, i.e. be invariant under left translation by matrices from $\mathrm{GL}_2(L)$ and transform under left translation by the central scalar matrix attached to an idele $z$ by the factor $\xi_L(z)$; assume further that $v$ lies in $L^2$ for the Haar measure restricted to $\Phi_L$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be arbitrary. Then $$\int_{\Phi_0} \Big(\int_{\mathrm{GL}_2(\mathbb{A}_L)} u\big(\sigma_{\mathbb{A}}(x y)\big)\,\varphi(y)\,dy\Big)\,\overline{v(x)}\,dx = 0,$$ where $\sigma_{\mathbb{A}}$ is the action of $\sigma$ on $\mathrm{GL}_2(\mathbb{A}_L)$ induced by $D$, the inner integral being `twistedConvOp K L D σ φ u`, the right convolution by $\varphi$ of $u \circ \sigma_{\mathbb{A}}$, and both integrals being Bochner integrals against `adelicGLHaar`, hence $0$ where the integrand fails to be integrable.
--
--   This is the orthogonality statement that kills the contribution of a twisted convolution operator to a trace computation whenever the central character in play is moved by the Galois twist: the integrand transforms by the factor $\xi_L(\sigma_{\mathbb{A}} z)\overline{\xi_L(z)} \neq 1$ under translation by a norm-one idele preserving the slab. It is used in the evaluation of the twisted cut trace on slab fundamental domains, where it allows all non-$\sigma$-invariant isotypic components to be discarded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab.lean

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

theorem AutomorphicForm.setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hne : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ ≠
        ξL ⟨z, Subgroup.mem_top z⟩)
    (u v : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξL u) (hv : IsLsXiFunction (𝓞 L) L ⊤ ξL v)
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) :
    ∫ x in Φ₀, twistedConvOp K L D σ φ u x * conj (v x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by sorry
