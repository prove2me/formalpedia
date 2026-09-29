-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_chiDet_sigmaAdelicAct_mul_chiDet_inv_eq_zero_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.setIntegral_chiDet_sigmaAdelicAct_mul_chiDet_inv_eq_zero_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/13988d80-a568-5579-bcad-6531ce743d80
-- title:
--   Vanishing of a twisted determinant-character integral over a fundamental domain
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ consist of a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from the $K$-automorphisms of $L$ to the continuous ring automorphisms of the adele ring $\mathbb{A}_L$ which on principal adeles agrees with the action on $L$, and let $\sigma$ be a $K$-automorphism of $L$. Let $\alpha, \beta$ be reals and write $S = \{g \in \mathrm{GL}_2(\mathbb{A}_L) : \|\det g\| \in [\alpha,\beta]\}$, where $\|x\|$ denotes the real value of the distributive Haar character of $\mathbb{A}_L$ at the idele $x$. Let $\Phi \subseteq S$ be a fundamental domain for the action of the image of $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ (entrywise application of $L \to \mathbb{A}_L$) on $\mathrm{GL}_2(\mathbb{A}_L)$, taken with respect to the Haar measure `adelicGLHaar` for the Borel structure `glBorel`, restricted to $S$. Let $\chi : \mathbb{A}_L^\times \to \mathbb{C}^\times$ be a homomorphism which is trivial on the image of $L^\times$, and assume there is an idele $z$ with $\chi(D.\mathrm{act}\,\sigma(z)) \neq \chi(z)$. Then $\int_\Phi \chi\big(\det(\sigma_{\mathbb{A}} x)\big)\,\chi(\det x)^{-1}\, dx = 0$, the integral being against the unrestricted Haar measure, where $\sigma_{\mathbb{A}}$ acts on $\mathrm{GL}_2(\mathbb{A}_L)$ entrywise through $D.\mathrm{act}\,\sigma$. No continuity is assumed of $\chi$, and no inequality between $\alpha$ and $\beta$.
--
--   This is the orthogonality, or vanishing, step for the non-invariant idele class character $(\chi \circ \sigma_{\mathbb{A}})\chi^{-1}$ on a determinant slab in $\mathrm{GL}_2(\mathbb{A}_L)$, familiar from the base-change comparison of trace formulae. It feeds the construction of atomic test functions in [`AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv`](thm.html#AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_chiDet_sigmaAdelicAct_mul_chiDet_inv_eq_zero_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_chiDet_sigmaAdelicAct_mul_chiDet_inv_eq_zero_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hχt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range → χ z = 1)
    (hne : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
      χ (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z) ≠ χ z) :
    ∫ x in Φ, chiDet (𝓞 L) L χ (sigmaAdelicAct K L D σ x) * chiDet (𝓞 L) L χ⁻¹ x
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by sorry
