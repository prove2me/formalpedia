-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
-- name    : CuspForm.IsAdelicLiftOf.apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/fea448df-c364-561e-8d5c-3264118c323a
-- title:
--   Level and nebentypus of a K₁(qᵃ)-fixed vector in a twisted lift
-- statement:
--   Let $M\ge 1$, let $g$ be a cusp form of weight $2$ on $\Gamma_0(M)$ and let $\Phi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ satisfy `IsAdelicLiftOf`: $\Phi$ is invariant under left translation by the image of $\mathrm{GL}_2(\mathbb{Q})$, invariant under right translation by the finite-adelic level-one group of the ideal $(M)$ embedded with trivial archimedean component, and $\Phi(h)=(g\mid_2 h_\infty)(i)$ whenever the finite component of $h$ is $1$ and its real component has positive determinant. Let $q$ be a prime, let $\eta:\mathbb{A}_{\mathbb{Q}}^\times\to\mathbb{C}^\times$ be a homomorphism trivial on the principal ideles and admitting the modulus $(q^b)$ (it kills every idele with trivial archimedean part whose finite components are units and are $\equiv 1$ to the multiplicity prescribed by $(q^b)$), and write $\Phi'=(\eta\circ\det)\cdot\Phi$. Let $a\in\mathbb{N}$, let $\theta:\mathbb{Z}_q^\times\to\mathbb{C}^\times$ be a homomorphism, and let $y$ lie in the span of the adelic right translates of $\Phi'$, assumed moreover to lie in the $\mathbb{C}$-span of the translates of $\Phi'$ by $\mathrm{GL}_2(\mathbb{Q}_q)$, to be fixed by the subgroup of $\mathrm{GL}_2(\mathbb{Q}_q)$ of matrices coming from $\mathrm{GL}_2(\mathbb{Z}_q)$ with $(1,0)$-entry in $(q^a)$ and $(1,1)$-entry $\equiv 1 \bmod q^a$, and to satisfy $\mathrm{diag}(u,u)\cdot y=\theta(u)\,y$ for all $u\in\mathbb{Z}_q^\times$. Put $N=q^{\max(a,1)}\cdot M/q^{v_q(M)}$. Then, writing $y$ also for the associated function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$: first, $y(\gamma z)=y(z)$ for all $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and all $z$; second, for every $u$ in the finite-adelic level-zero group of $(N)$ (i.e. $u$ and $u^{-1}$ have integral entries and lower-left entry in the ball of radius the ideal bound of $(N)$) and every $d\in\mathbb{Z}_q^\times$ such that the $q$-component of the $(1,1)$-entry of $u$ differs from the image of $d$ by an element of valuation at most the ideal bound of $(N)$ at $q$, one has $y(z\cdot u)=\theta(d)\,y(z)$ for all $z$, where $u$ is embedded with trivial archimedean component.
--
--   This is the level computation underlying the passage from an adelic vector with a prescribed central character to a classical modular form on $\Gamma_1(N)$ with nebentypus: at $q$ the local component of an element of $K_0(N)$ is split as a central unit times an element of $K_1(q^{v_q(N)})$, while away from $q$ the levels $N$ and $M$ agree. It is used by [`CuspForm.IsAdelicLiftOf.exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed`](thm.html#CuspForm.IsAdelicLiftOf.exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed) and by [`CuspForm.IsNewform.exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq`](thm.html#CuspForm.IsNewform.exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : AutomorphicForm.IsIdeleClassChar (NumberField.RingOfIntegers ℚ) ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    (a : ℕ) (θ : ℤ_[q]ˣ →* ℂˣ)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ,
      LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y) :
    (∀ (γ : GL (Fin 2) ℚ) (z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
        (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn
            (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * z) =
          (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn z) ∧
    ∀ u ∈ NumberField.AdelicLevel.finiteLevelZero (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))),
      ∀ d : ℤ_[q]ˣ,
        Valued.v
            (((u : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) 1 1)
                (AdelicDock.padicPlace q) -
              AdelicDock.padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q])) ≤
          NumberField.AdelicLevel.idealBound (NumberField.RingOfIntegers ℚ)
            (AdelicDock.ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))) (AdelicDock.padicPlace q) →
        ∀ z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
          (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn
              (z * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) =
            (θ d : ℂ) * (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn z := by sorry
