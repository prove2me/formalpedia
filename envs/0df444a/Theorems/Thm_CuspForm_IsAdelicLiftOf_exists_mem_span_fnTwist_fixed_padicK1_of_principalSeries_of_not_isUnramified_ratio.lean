-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fnTwist_fixed_padicK1_of_principalSeries_of_not_isUnramified_ratio
-- name    : CuspForm.IsAdelicLiftOf.exists_mem_span_fnTwist_fixed_padicK1_of_principalSeries_of_not_isUnramified_ratio
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/252c0a0f-6a94-5168-a421-28d948ef3f84
-- title:
--   Twisting a ramified-ratio principal series to K₁(qᵇ)-fixed vectors
-- statement:
--   Let $M$ be a nonzero natural number and $g$ a cusp form of weight $2$ for $\Gamma_0(M)$, and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $g$ in the sense of [`CuspForm.IsAdelicLiftOf`](def/CuspForm_AdelicLift.html#L14): $\Phi$ is invariant under left translation by the global points $\mathrm{GL}_2(\mathbb{Q})$, invariant under right translation by the finite level-one group attached to [`AdelicDock.ratLevel M`](def/AdelicDock_LocalEmbedding.html#L303), and on adelic matrices with trivial finite part and archimedean component in $\mathrm{GL}_2^{+}(\mathbb{R})$ it is given by the weight-$2$ slash action of $g$ evaluated at $i$. Let $q$ be a prime, $\mu_1,\mu_2 \colon \mathbb{Q}_q^{\times} \to \mathbb{C}^{\times}$ characters, and $f$ a nonzero $\mathbb{C}$-linear map from the module [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) of $\Phi$ to the principal-series space [`LocalNewvector.PSCarrier q μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173) satisfying $f(x \cdot v) = x \cdot f(v)$ for all $x \in \mathrm{GL}_2(\mathbb{Q}_q)$. Let $b$ be a natural number and $\chi_0$ a character of $(\mathbb{Z}/q^b)^{\times}$ such that $\mu_1(u) = \chi_0(u \bmod q^b)$ for every $u \in \mathbb{Z}_q^{\times}$, and assume $\mu_1^{-1}\mu_2$ is not unramified, i.e. it is not the case that $\mu_1^{-1}\mu_2(u) = 1$ for all $u \in \mathbb{Q}_q^{\times}$ with $\|u\| = 1$. Let $\eta$ be a character of the idele group of $\mathbb{Q}$ such that for every $u \in \mathbb{Z}_q^{\times}$ the value of $\eta$ at the idele with component $u$ at the place $q$ (transported by [`AdelicDock.padicRingEquiv`](def/AdelicDock_LocalEmbedding.html#L234)) and $1$ elsewhere equals $\chi_0(u \bmod q^b)^{-1}$. Then there is an element $y$ of the module [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) of the twisted function [`AutomorphicForm.fnTwist ℚ η Φ`](def/AutomorphicForm_FnTwist.html#L12), the pointwise product of $\Phi$ with the determinant character `chiDet` of $\eta$, such that: $y$ lies in the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the distinguished element [`LocalNewvector.AdelicSpan.self`](def/LocalNewvector_AdelicSpanCarrier.html#L121) of that module; $y \neq 0$; $y$ is fixed by every element of the subgroup [`LocalNewvector.padicK1 q b`](def/LocalNewvector_CongruenceSubgroupK1.html#L161); and for every $u \in \mathbb{Z}_q^{\times}$ the scalar matrix with diagonal entry $u$ acts on $y$ by the square of the above value of $\eta$ at $u$.
--
--   This is the local newvector step at the prime $q$ in the ramified-ratio principal-series case: a nonzero equivariant map to $B(\mu_1,\mu_2)$ is converted, after twisting the adelic function by the character $\eta$ of the ideles, into a nonzero vector fixed by $K_1(q^b)$ on which the central units at $q$ act through the square of $\eta$. It feeds the construction of a normalised eigenform of divided level in [`WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_isNewform_of_factorization_eq_two`](thm.html#WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_isNewform_of_factorization_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fnTwist_fixed_padicK1_of_principalSeries_of_not_isUnramified_ratio.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.Padics.RingHoms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.exists_mem_span_fnTwist_fixed_padicK1_of_principalSeries_of_not_isUnramified_ratio
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (hχ₀compat : ∀ u : ℤ_[q]ˣ,
      μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) =
        χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))
    (hratio : ¬ LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂))
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηu : ∀ u : ℤ_[q]ˣ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u))))
        = (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) :
    ∃ y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ),
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q b) (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      ∀ u : ℤ_[q]ˣ, LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
        ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
            (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
              (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
                (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2) • y := by sorry
