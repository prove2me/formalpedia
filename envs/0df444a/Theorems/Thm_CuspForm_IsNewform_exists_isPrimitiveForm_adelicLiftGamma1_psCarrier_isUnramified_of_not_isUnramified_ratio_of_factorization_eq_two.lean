-- Prove2me | Theorems.Thm_CuspForm_IsNewform_exists_isPrimitiveForm_adelicLiftGamma1_psCarrier_isUnramified_of_not_isUnramified_ratio_of_factorization_eq_two
-- name    : CuspForm.IsNewform.exists_isPrimitiveForm_adelicLiftGamma1_psCarrier_isUnramified_of_not_isUnramified_ratio_of_factorization_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/677bdd5e-9ad1-51f6-bbd9-bde33f613a10
-- title:
--   Ramified principal series at q with v_q(M)=2: twist of level exactly q
-- statement:
--   Let $M$ be a positive integer and $g$ a weight-two cusp form on $\Gamma_0(M)$ which is a newform, i.e. $g$ is a normalised eigenform ($a_1(g)=1$, multiplicativity of the $q$-expansion coefficients on coprime arguments, and the two prime-power recursions according as $p \mid M$ or not) and for no proper divisor $M_0$ of $M$ does a normalised eigenform on $\Gamma_0(M_0)$ share the coefficients $a_\ell$ at all primes $\ell \nmid M$. Let $q$ be a prime and $\Phi$ a nonzero complex-valued function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $g$: it is left invariant under the image of $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the finite level-one subgroup attached to the ideal $(M)$, and on matrices with trivial finite component and archimedean component in $\mathrm{GL}_2^+(\mathbb{R})$ it is given by $(g \mid_2 h_\infty)(i)$. Let $\mu_1, \mu_2 : \mathbb{Q}_q^\times \to \mathbb{C}^\times$ be group homomorphisms and $f$ a nonzero $\mathbb{C}$-linear map from the span of the $\mathrm{GL}_2$-translates of $\Phi$ to the principal series space of locally constant functions on $\mathrm{GL}_2(\mathbb{Q}_q)$ transforming under the Borel by $\mu_1, \mu_2$ and the half modulus, which is $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant. Assume the ratio $\mu_1^{-1}\mu_2$ is ramified, that is, some $u \in \mathbb{Q}_q^\times$ with $\|u\| = 1$ has $(\mu_1^{-1}\mu_2)(u) \neq 1$, and that $q$ occurs in $M$ with exponent exactly $2$. Then there exist a positive integer $M'$, a Dirichlet character $\varepsilon$ modulo $M'$, a weight-two cusp form $h$ on $\Gamma_1(M')$ that is a primitive form for $\varepsilon$ (a normalised eigenform with nebentypus $\varepsilon$ in the above sense, whose eigenpacket occurs at no proper divisor of $M'$), an adelic lift $\Phi'$ of $h$ in the corresponding $\Gamma_1$ sense, homomorphisms $\nu_1, \nu_2 : \mathbb{Q}_q^\times \to \mathbb{C}^\times$ and a nonzero $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant $\mathbb{C}$-linear map from the span of the translates of $\Phi'$ to the principal series space for $\nu_1, \nu_2$, such that $\nu_1$ is unramified, $q \mid M'$, $q^2 \nmid M'$, and for every prime $\ell \nmid M$ and every unit $u$ of $\mathbb{Z}_q$ whose image in $\mathbb{Q}_q$ is $\ell$ one has $a_\ell(h) = \mu_1(u)\, a_\ell(g)$ and $\varepsilon(\ell \bmod M') = \mu_1(u)^2$.
--
--   This is the twisting statement of Atkin–Li and Shimura in the case of conductor exponent two at $q$, recording that the primitive twist has level exactly divisible by the first power of $q$. It strengthens the unconditional twisting result by adding the conclusions $q \mid M'$ and $q^2 \nmid M'$, and feeds the computation of the characteristic polynomial of inertia at $q$ on the $q$-adic Galois representation attached to $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_exists_isPrimitiveForm_adelicLiftGamma1_psCarrier_isUnramified_of_not_isUnramified_ratio_of_factorization_eq_two.lean

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

theorem CuspForm.IsNewform.exists_isPrimitiveForm_adelicLiftGamma1_psCarrier_isUnramified_of_not_isUnramified_ratio_of_factorization_eq_two
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : ¬ LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂))

    (hM2 : M.factorization q = 2) :
    ∃ (M' : ℕ) (_ : NeZero M') (ε : DirichletCharacter ℂ M')
      (h : CuspForm (CongruenceSubgroup.Gamma1 M') 2) (_ : CuspForm.IsPrimitiveForm ε h)
      (Φ' : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
      (_ : CuspForm.IsAdelicLiftOfGamma1 h Φ')
      (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ)
      (f' : LocalNewvector.AdelicSpan Φ' →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ'), f' (x • v) = x • f' v) ∧
      f' ≠ 0 ∧ LocalNewvector.IsUnramified q ν₁ ∧

      q ∣ M' ∧ ¬ q ^ 2 ∣ M' ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ∀ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = ℓ →
        ModularFormClass.qCoeff h ℓ =
            (μ₁ (Units.map (PadicInt.Coe.ringHom : ℤ_[q] →+* ℚ_[q]).toMonoidHom u) : ℂ) *
              ModularFormClass.qCoeff g ℓ ∧
          ε (ℓ : ZMod M') =
            (μ₁ (Units.map (PadicInt.Coe.ringHom : ℤ_[q] →+* ℚ_[q]).toMonoidHom u) : ℂ) ^ 2 := by sorry
