-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform
-- name    : CuspForm.IsAdelicLiftOf.heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/a53f8549-e714-5c46-9afd-2ff2fa5e1a28
-- title:
--   Hecke action on full-level components of an adelic newform
-- statement:
--   Fix $M'\ge 1$ and a prime $q$. Let $g$ be a weight-two cusp form on $\Gamma_0(q^2M')$ which is a newform in the sense of the project: $g$ is a normalized eigenform (its $q$-expansion coefficient at $1$ is $1$, the coefficients are multiplicative at coprime arguments and satisfy the usual recursions at prime powers, with the two cases according to whether the prime divides the level), and for no proper divisor $M$ of $q^2M'$ does there exist a normalized eigenform of level $M$ whose coefficients at the primes not dividing $q^2M'$ agree with those of $g$. Let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ that is an adelic lift of $g$: it is left invariant under the global points $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the level-one subgroup at the ideal $(q^2M')$, and at every $h$ with trivial finite part and archimedean part of positive determinant one has $\Phi(h)=(g\mid_2 h_\infty)(i)$, where $h_\infty$ denotes the real matrix `ratArchGL2 h`. Let $y$ be an element of the span of the $\mathrm{GL}_2(\mathbb{A})$-translates of $\Phi$ which lies in the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of $\Phi$ itself and is fixed by `gl2CongruenceSubgroup q 1`, the subgroup of $x\in\mathrm{GL}_2(\mathbb{Q}_q)$ all of whose entries of $x-1$ and of $x^{-1}-1$ have norm at most $q^{-1}$. Let $\ell$ be a prime not dividing $q^2M'$, let $\ell_q\in\mathbb{Z}_q^\times$ be a unit with image $\ell$, and let $u\in\mathbb{Z}_q^\times$. Let $F,F_u$ be weight-two cusp forms on $\Gamma(q)\cap\Gamma_0(M')$ which represent the components of $y$ at $u\ell_q^{-1}$ and at $u$, meaning that for every $h$ with trivial finite part and positive archimedean determinant the value of the function underlying $y$ at $h\cdot\iota_q(\mathrm{diag}(u\ell_q^{-1},1))$ equals $(F\mid_2 h_\infty)(i)$, and likewise for $\mathrm{diag}(u,1)$ and $F_u$, where $\iota_q$ is the embedding of $\mathrm{GL}_2(\mathbb{Q}_q)$ into the adelic group. Finally let $F',F_u'$ be weight-two cusp forms on $\Gamma_H(q^2M')$, with $H$ the kernel of $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$, whose underlying functions are $F\mid_2\mathrm{diag}(q,1)$ and $F_u\mid_2\mathrm{diag}(q,1)$. Then $T_\ell F' = a_\ell(g)\, F_u'$, where $a_\ell(g)$ is the $\ell$-th $q$-expansion coefficient of $g$ and $T_\ell$ is [`CuspForm.heckeTLinH 2 hℓ hℓN`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224), the $\mathbb{C}$-linear endomorphism of weight-two cusp forms on $\Gamma_H(q^2M')$ given by $f\mapsto U_\ell f + f\mid_2(\gamma\,\mathrm{diag}(\ell,1))$ for a lift $\gamma\in\Gamma_0(q^2M')$ with lower-right entry congruent to $\ell$, when this formula preserves the space, and by $0$ otherwise.
--
--   This is the Hecke compatibility of the full-level components of the adelic vector attached to a newform of level $q^2M'$: applying the classical Hecke operator $T_\ell$ to the component indexed by $u\ell_q^{-1}$ reproduces $a_\ell(g)$ times the component indexed by $u$. It feeds the construction of $\Gamma_H$-level Hecke eigenvectors in the cohomology and in the Tate module of the Jacobian of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.IsAdelicLiftOf.heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2} (hg : g.IsNewform)
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M') (ℓq : ℤ_[q]ˣ) (hℓq : (ℓq : ℤ_[q]) = ℓ)
    (u : ℤ_[q]ˣ)
    (F Fu : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2)
    (hF : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹)))) =
              ((⇑F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I)
    (hFu : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
              ((⇑Fu) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I)
    (F' Fu' : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)
    (hF' : ⇑F' = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q)
    (hFu' : ⇑Fu' = (⇑Fu) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    CuspForm.heckeTLinH 2 hℓ hℓN F' = (ModularFormClass.qCoeff g ℓ : ℂ) • Fu' := by sorry
