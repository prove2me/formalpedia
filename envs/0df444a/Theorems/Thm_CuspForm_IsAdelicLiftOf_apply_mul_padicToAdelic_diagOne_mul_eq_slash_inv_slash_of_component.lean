-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
-- name    : CuspForm.IsAdelicLiftOf.apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/9658e177-c9ec-5255-9380-cf3901c84066
-- title:
--   Component at u of a k-translate is F∣₂γ⁻¹
-- statement:
--   Fix a positive integer $M'$ and a prime $q$. Let $g$ be a weight-$2$ cusp form on $\Gamma_0(q^2M')$ and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ which is an adelic lift of $g$: it is invariant under left translation by the image of $\mathrm{GL}_2(\mathbb{Q})$, invariant under right translation by the finite level-one subgroup attached to the ideal $(q^2M')$, and satisfies $\Phi(h)=(g\mid_2 h_\infty)(i)$ for every $h$ whose finite part is $1$ and whose archimedean image $h_\infty$ has positive determinant. Let $y$ lie in the span of the $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$-translates of $\Phi$, assumed to lie in the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of $\Phi$ itself and to be fixed by every element of the congruence subgroup of $\mathrm{GL}_2(\mathbb{Q}_q)$ cut out by $\|(g-1)_{ij}\|\le q^{-1}$ and $\|(g^{-1}-1)_{ij}\|\le q^{-1}$. Let $k$ lie in the corresponding subgroup at radius $1$, with integral lift $k_0\in\mathrm{GL}_2(\mathbb{Z}_q)$ and reduction $\bar k\in\mathrm{GL}_2(\mathbb{Z}/q)$, let $u\in\mathbb{Z}_q^\times$, and put $u'=u\det k_0$. Let $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ satisfy $\gamma\in\Gamma(M')$ and, entrywise modulo $q$, $\gamma\equiv\mathrm{diag}(\bar u,1)\,\bar k\,\mathrm{diag}(\bar u',1)^{-1}$. Finally let $F$ be a weight-$2$ cusp form on $\Gamma(q)\cap\Gamma_0(M')$ such that for every $h$ with trivial finite part and $\det h_\infty>0$ one has $y\bigl(h\,\iota_q(\mathrm{diag}(u',1))\bigr)=(F\mid_2 h_\infty)(i)$, where $\iota_q$ denotes the embedding of $\mathrm{GL}_2(\mathbb{Q}_q)$ into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$. Then for every such $h$, $y\bigl(h\,\iota_q(\mathrm{diag}(u,1)\,k)\bigr)=\bigl((F\mid_2\gamma^{-1})\mid_2 h_\infty\bigr)(i)$, the slash being taken with the image of $\gamma^{-1}$ in $\mathrm{GL}_2(\mathbb{R})$.
--
--   This is the transformation rule for the classical components of an adelic vector of full level $q$: translating by $k\in\mathrm{GL}_2(\mathbb{Z}_q)$ sends the component at $u\det k$ to the component at $u$ slashed by a matrix $\gamma\in\Gamma(M')$ realising the prescribed reduction modulo $q$. It is used in the construction of the family of level-$\Gamma(q)\cap\Gamma_0(M')$ forms attached to such a vector and, through that, in producing an injection of the relevant Tate module of the Jacobian of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.IsAdelicLiftOf.apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ))
    (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (u : ℤ_[q]ˣ)
    (γ : SL(2, ℤ)) (hγM : γ ∈ CongruenceSubgroup.Gamma M')
    (hγq : ∀ i j : Fin 2, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) =
      ((CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) *
          LocalNewvector.gl2ReductionHom q k *
          (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom
            (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k))))⁻¹ : CuspidalType.GL2 q) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) i j)
    (F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2)
    (hF : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom
                    (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k))))) =
              ((⇑F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          (LocalNewvector.AdelicSpan.toFn Φ y).toFn
              (h * AdelicDock.padicToAdelic q
                (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) *
                  (k : GL (Fin 2) ℚ_[q]))) =
            (((⇑F) ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h)
              UpperHalfPlane.I := by sorry
