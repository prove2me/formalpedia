-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed
-- name    : CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/f0ab5e98-253c-5a24-b642-46cf5283e071
-- title:
--   Twisted descent: lowered-level eigenform with η-twisted coefficients
-- statement:
--   Let $M$ be a nonzero natural number and let $g$ be a weight-two cusp form on $\Gamma_0(M)$ which is a normalised eigenform in the sense of the project structure `IsNormalizedEigenform`: its first $q$-expansion coefficient is $1$, its coefficients are multiplicative on coprime indices, and they satisfy the recursion $a_{p^{r+2}}=a_pa_{p^{r+1}}-p\,a_{p^r}$ at primes $p\nmid M$ and $a_{p^{r+2}}=a_pa_{p^{r+1}}$ at primes $p\mid M$. Let $q$ be a prime and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $g$, i.e. left invariant under the global points $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the finite level-one subgroup attached to the ideal $(M)$, and such that at every adelic matrix trivial at the finite places whose archimedean component has positive determinant the value of $\Phi$ is $(g\mid_2 \cdot)(i)$ evaluated at that archimedean component. Let $\eta$ be a character of the idele units of $\mathbb{Q}$ which is an idele class character, continuous and of finite order, and which admits the modulus $(q^b)$ for some $b$, in the sense that $\eta(u)=1$ for every idele unit with trivial archimedean component all of whose finite components have valuation $1$ and satisfy the congruence condition $v(u_v-1)\le \exp(-\mathrm{ord}_v(q^b))$. Let $a\le v_q(M)$. Write $\Phi'=(\eta\circ\det)\cdot\Phi$ for the twist [`AutomorphicForm.fnTwist`](def/AutomorphicForm_FnTwist.html#L12), and suppose $y$ is an element of the associated space [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) of $\Phi'$ which lies in the complex span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-orbit of the distinguished element [`LocalNewvector.AdelicSpan.self`](def/LocalNewvector_AdelicSpanCarrier.html#L121), is nonzero, is fixed by the congruence subgroup [`LocalNewvector.padicK1 q a`](def/LocalNewvector_CongruenceSubgroupK1.html#L161) of $\mathrm{GL}_2(\mathbb{Q}_q)$, and is fixed by $\mathrm{centralGL}_q(z)$ for every $z\in\mathbb{Q}_q^\times$. Then there exists a weight-two cusp form $h$ on $\Gamma_0\big(M/q^{\,v_q(M)-a}\big)$ which is a normalised eigenform in the same sense and whose coefficients satisfy $a_\ell(h)=\eta(\varpi_\ell)\,a_\ell(g)$ for every prime $\ell$ with $\ell\nmid M$ and $\ell\ne q$, where $\varpi_\ell$ is the idele [`AutomorphicForm.uniformizerIdele`](def/AutomorphicForm_HeckeEigenfunction.html#L31) at the place of $\mathbb{Q}$ above $\ell$.
--
--   This is the twisting version of the adelic descent step: from a vector in the local $\mathrm{GL}_2(\mathbb{Q}_q)$-span of the $\eta$-twist of an adelic lift, invariant under a $K_1(q^a)$-type congruence subgroup and under the centre, one produces a normalised eigenform at the correspondingly lowered level whose coefficients away from $Mq$ are those of $g$ multiplied by the local values of $\eta$ at unramified uniformizers. It is used in the construction of quadratic twists of newforms down to exponent one at $q$, which feeds the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    (a : ℕ) (hae : a ≤ M.factorization q)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hy₀ : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y = y) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 (M / q ^ (M.factorization q - a))) 2, h.IsNormalizedEigenform ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ≠ q →
        ModularFormClass.qCoeff h ℓ =
          (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) * ModularFormClass.qCoeff g ℓ := by sorry
