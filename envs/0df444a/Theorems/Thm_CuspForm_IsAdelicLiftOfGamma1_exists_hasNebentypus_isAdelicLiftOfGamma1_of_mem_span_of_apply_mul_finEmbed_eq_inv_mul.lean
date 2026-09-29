-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
-- name    : CuspForm.IsAdelicLiftOfGamma1.exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/572ac4f2-1b3c-5642-b1be-1ed6b67a07ea
-- title:
--   Descent from a nebentypus eigenvector to S₂(Γ₁(N),ε)
-- statement:
--   Let $M\ge 1$, let $h$ be a weight-two cusp form for $\mathrm{CongruenceSubgroup.Gamma1}\ M$, and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ which is an adelic lift of $h$ in the sense of [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14): $\Phi$ is invariant under left multiplication by the image of $\mathrm{GL}_2(\mathbb{Q})$ under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), invariant under right multiplication by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of every element of the subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418) attached to the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$, and satisfies $\Phi(g)=(h\mid_2 \mathrm{ratArchGL2}(g))(i)$ whenever `AdelicLevel.glFin` of $g$ is $1$ and $\mathrm{ratArchGL2}(g)$ lies in $\mathrm{GL}_2^{+}(\mathbb{R})$. Let $N\ge 1$, let $\varepsilon$ be a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and let $y$ be an element of [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$, i.e. of the $\mathbb{C}$-span of the $\mathrm{GL}_2$-translates of $\Phi$, which is assumed to lie in the $\mathbb{C}$-span of the translates of the distinguished generator by elements `finEmbed` $u$ with $u\in\mathrm{GL}_2$ of the finite adeles. Assume further that for every $u$ in [`NumberField.AdelicLevel.finiteLevelZero`](def/NumberField_AdelicLevel.html#L410) for the ideal $(N)$, every integer $d$ coprime to $N$ whose image satisfies that $u_{11}-d$ lies in [`NumberField.AdelicLevel.idealBall`](def/NumberField_AdelicLevel.html#L230) for $(N)$, and every $x$, the function attached to $y$ satisfies $y(x\cdot \mathrm{finEmbed}(u))=\varepsilon(d)^{-1}y(x)$. Then there exists a weight-two cusp form $F$ for $\mathrm{Gamma1}\ N$ such that $F$ has nebentypus $\varepsilon$, namely $F(\gamma\tau)=\varepsilon(\gamma_{11})\,(\gamma_{10}\tau+\gamma_{11})^2F(\tau)$ for all $\gamma\in\mathrm{SL}_2(\mathbb{Z})\cap\Gamma_0(N)$ and all $\tau$ in the upper half-plane; $F$ is an adelic lift, in the above sense at level $N$, of the function attached to $y$; and $F=0$ forces $y=0$.
--
--   This is the descent half of the classical dictionary between $S_2(\Gamma_1(N),\varepsilon)$ and functions on $\mathrm{GL}_2(\mathbb{Q})\backslash\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})/K_1(N)$ on which $K_0(N)/K_1(N)\cong(\mathbb{Z}/N)^{\times}$ acts through $\varepsilon^{-1}$, applied to vectors in the span of finite-adelic translates of the lift of a given weight-two form. It is used in the analysis of level structures of primitive forms, being cited by [`CuspForm.IsPrimitiveForm.factorization_le_of_mem_span_of_mem_fixedSubmodule_padicK1`](thm.html#CuspForm.IsPrimitiveForm.factorization_le_of_mem_span_of_mem_fixedSubmodule_padicK1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.lean

import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOfGamma1.exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun u :
      GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) =>
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u :
          AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) • LocalNewvector.AdelicSpan.self Φ))
    (hK0 : ∀ u ∈ NumberField.AdelicLevel.finiteLevelZero (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ d : ℤ, IsCoprime d (N : ℤ) →
        (u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) 1 1
            - algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (d : ℚ)
          ∈ NumberField.AdelicLevel.idealBall (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N) →
        ∀ x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
          (LocalNewvector.AdelicSpan.toFn Φ y).toFn (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u)
            = (ε (d : ZMod N))⁻¹ * (LocalNewvector.AdelicSpan.toFn Φ y).toFn x) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma1 N) 2,
      CuspForm.HasNebentypus ε F ∧
      CuspForm.IsAdelicLiftOfGamma1 F (LocalNewvector.AdelicSpan.toFn Φ y).toFn ∧
      (F = 0 → y = 0) := by sorry
