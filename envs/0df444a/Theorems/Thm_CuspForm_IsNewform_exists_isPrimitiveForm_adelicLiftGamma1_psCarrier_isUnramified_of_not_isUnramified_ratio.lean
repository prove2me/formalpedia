-- Prove2me | Theorems.Thm_CuspForm_IsNewform_exists_isPrimitiveForm_adelicLiftGamma1_psCarrier_isUnramified_of_not_isUnramified_ratio
-- name    : CuspForm.IsNewform.exists_isPrimitiveForm_adelicLiftGamma1_psCarrier_isUnramified_of_not_isUnramified_ratio
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/cac74b65-e3b0-5096-a003-8a3c6ecbb173
-- title:
--   Twisting a newform to unramified principal-series character at q
-- statement:
--   Let $M\ge 1$ and let $g$ be a weight-two cusp form on $\Gamma_0(M)$ which is a newform, i.e. $g$ is a normalized eigenform and for no proper divisor of $M$ does there exist a normalized eigenform on that smaller level agreeing with $g$ in all $q$-coefficients at primes not dividing $M$. Let $q$ be prime and let $\Phi\neq 0$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $g$: invariant on the left under the global points $\mathrm{GL}_2(\mathbb{Q})$, invariant on the right under the level-one finite subgroup attached to the ideal $(M)$, and equal, at adelic points with trivial finite part and archimedean part in $\mathrm{GL}_2^{+}(\mathbb{R})$, to the weight-two slash action of $g$ evaluated at $i$. Let $\mu_1,\mu_2:\mathbb{Q}_q^{\times}\to\mathbb{C}^{\times}$ be characters and let $f$ be a nonzero $\mathbb{C}$-linear map from [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) of $\Phi$ to the principal series space attached to $(\mu_1,\mu_2)$ satisfying $f(x\cdot v)=x\cdot f(v)$ for all $x\in\mathrm{GL}_2(\mathbb{Q}_q)$, and assume $\mu_1^{-1}\mu_2$ is ramified, i.e. it is not identically $1$ on the norm-one units of $\mathbb{Q}_q$. Then there exist a level $M'\ge 1$, a Dirichlet character $\varepsilon$ modulo $M'$ with values in $\mathbb{C}$, a weight-two form $h$ on $\Gamma_1(M')$ which is primitive with nebentypus $\varepsilon$ (a normalized eigenform for the Hecke relations away from $M'$, multiplicative at primes dividing $M'$, with nebentypus $\varepsilon$, whose eigenpacket occurs at no proper divisor of $M'$), a function $\Phi'$ which is an adelic lift of $h$ in the $\Gamma_1$ sense, characters $\nu_1,\nu_2:\mathbb{Q}_q^{\times}\to\mathbb{C}^{\times}$, and a nonzero $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant $\mathbb{C}$-linear map from [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) of $\Phi'$ to the principal series space attached to $(\nu_1,\nu_2)$, such that $\nu_1$ is unramified and such that for every prime $\ell$ not dividing $M$ and every $u\in\mathbb{Z}_q^{\times}$ whose image in $\mathbb{Q}_q$ is $\ell$ one has $a_\ell(h)=\mu_1(u)\,a_\ell(g)$ and $\varepsilon(\ell \bmod M')=\mu_1(u)^2$.
--
--   This is the automorphic step in the classical reduction, by twisting by a suitable Dirichlet (equivalently Hecke) character, of the case of a ramified principal series at $q$ to the case where one of the two inducing characters is unramified; the price is passage from $\Gamma_0(M)$ with trivial character to a primitive form on $\Gamma_1(M')$ with nebentypus, the twisting character being recorded by the relations $a_\ell(h)=\mu_1(u)a_\ell(g)$ and $\varepsilon(\ell)=\mu_1(u)^2$ at primes $\ell\nmid M$. It feeds the analysis of the local component at $q$ in the case that the conductor exponent equals two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_exists_isPrimitiveForm_adelicLiftGamma1_psCarrier_isUnramified_of_not_isUnramified_ratio.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNewform.exists_isPrimitiveForm_adelicLiftGamma1_psCarrier_isUnramified_of_not_isUnramified_ratio
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : ¬ LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂)) :
    ∃ (M' : ℕ) (_ : NeZero M') (ε : DirichletCharacter ℂ M')
      (h : CuspForm (CongruenceSubgroup.Gamma1 M') 2) (_ : CuspForm.IsPrimitiveForm ε h)
      (Φ' : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
      (_ : CuspForm.IsAdelicLiftOfGamma1 h Φ')
      (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ)
      (f' : LocalNewvector.AdelicSpan Φ' →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ'), f' (x • v) = x • f' v) ∧
      f' ≠ 0 ∧ LocalNewvector.IsUnramified q ν₁ ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ∀ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = ℓ →
        ModularFormClass.qCoeff h ℓ =
            (μ₁ (Units.map (PadicInt.Coe.ringHom : ℤ_[q] →+* ℚ_[q]).toMonoidHom u) : ℂ) *
              ModularFormClass.qCoeff g ℓ ∧
          ε (ℓ : ZMod M') =
            (μ₁ (Units.map (PadicInt.Coe.ringHom : ℤ_[q] →+* ℚ_[q]).toMonoidHom u) : ℂ) ^ 2 := by sorry
